-- Prove2me | solution 1 for WagerFairDiv.theorem_3_sideBetPO_of_pareto
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:29:43.767245+00:00
-- url     : https://prove2.me/submissions/2e46ce0e-0555-42c5-b16c-9503c44208f6

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

open WagerFairDiv in
theorem solution {n m : ℕ} (A B : WagerFairDiv.Mech n m) (hA : WagerFairDiv.IsAllocMech A)
    (hAB : WagerFairDiv.Corresponding A B) (hPO : WagerFairDiv.ParetoOptimal A) :
    WagerFairDiv.SideBetPO B := by
  intro p w h
  obtain ⟨db, hsum, hnn, hge, i0, hi0⟩ := h
  have htot : 0 < w.total := by
    unfold WagerFairDiv.PosVec.total
    exact Finset.sum_pos (fun k _ => w.2 k) ⟨i0, Finset.mem_univ _⟩
  let a' : Fin n → Fin m → ℝ := fun i j => A p w i j + db i j / w.total
  have hval : ∀ i, WagerFairDiv.val (p i).1 (a' i) =
      WagerFairDiv.val (p i).1 (A p w i) + WagerFairDiv.val (p i).1 (db i) / w.total := by
    intro i
    unfold WagerFairDiv.val
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by simp only [a']; ring)
  have feas : WagerFairDiv.IsFeasibleAlloc a' := by
    refine ⟨fun i j => ?_, fun j => ?_⟩
    · have e : a' i j = (B p w i j + db i j) / w.total := by
        simp only [a']
        rw [eq_div_iff htot.ne', add_mul, div_mul_cancel₀ _ htot.ne', hAB]
        ring
      rw [e]
      exact div_nonneg (hnn i j) htot.le
    · simp only [a']
      rw [Finset.sum_add_distrib, ← Finset.sum_div, hsum j, zero_div, add_zero]
      exact (hA p w).2 j
  obtain ⟨j, hj⟩ := hPO p w a' feas ⟨i0, by
    rw [hval]
    have := div_pos hi0 htot
    linarith⟩
  rw [hval] at hj
  have := div_nonneg (hge j) htot.le
  linarith
