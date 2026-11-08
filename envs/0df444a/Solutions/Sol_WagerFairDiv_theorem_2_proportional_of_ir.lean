-- Prove2me | solution 1 for WagerFairDiv.theorem_2_proportional_of_ir
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:13:47.534954+00:00
-- url     : https://prove2.me/submissions/a37acf80-216d-4eaa-b897-0fa45539c7e4

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

open WagerFairDiv in
theorem solution {n m : ℕ} (A B : WagerFairDiv.Mech n m) (hAB : WagerFairDiv.Corresponding A B)
    (hIR : WagerFairDiv.IndivRational B) (hIC : WagerFairDiv.WagerWeakIC B) :
    WagerFairDiv.Proportional A := by
  intro v e i
  obtain ⟨r, hr⟩ := hIR i (v i)
  have h1 := hr v e
  have h2 := hIC i (v i) (Function.update v i r) e
  rw [Function.update_idem, Function.update_eq_self] at h2
  have htot : 0 < e.total := by
    unfold WagerFairDiv.PosVec.total
    exact Finset.sum_pos (fun k _ => e.2 k) ⟨i, Finset.mem_univ _⟩
  have hv : WagerFairDiv.val (v i).1 (B v e i) = e.total * WagerFairDiv.val (v i).1 (A v e i) := by
    unfold WagerFairDiv.val
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hAB]
    ring
  rw [div_le_iff₀ htot]
  have h3 : e.1 i ≤ e.total * WagerFairDiv.val (v i).1 (A v e i) := by
    rw [← hv]; linarith
  linarith [mul_comm e.total (WagerFairDiv.val (v i).1 (A v e i))]
