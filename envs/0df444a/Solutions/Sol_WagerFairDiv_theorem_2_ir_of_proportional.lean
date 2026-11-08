-- Prove2me | solution 1 for WagerFairDiv.theorem_2_ir_of_proportional
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:07:50.879118+00:00
-- url     : https://prove2.me/submissions/045b5146-689b-45fa-90a4-78aec2653002

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

open WagerFairDiv in
theorem solution {n m : ℕ} (A B : WagerFairDiv.Mech n m) (hAB : WagerFairDiv.Corresponding A B)
    (hP : WagerFairDiv.Proportional A) : WagerFairDiv.IndivRational B := by
  intro i pi
  refine ⟨pi, fun p w => ?_⟩
  have h := hP (Function.update p i pi) w i
  rw [Function.update_self] at h
  have htot : 0 < w.total := by
    unfold WagerFairDiv.PosVec.total
    exact Finset.sum_pos (fun k _ => w.2 k) ⟨i, Finset.mem_univ _⟩
  have hv : WagerFairDiv.val pi.1 (B (Function.update p i pi) w i) =
      w.total * WagerFairDiv.val pi.1 (A (Function.update p i pi) w i) := by
    unfold WagerFairDiv.val
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hAB]
    ring
  rw [hv]
  rw [div_le_iff₀ htot] at h
  linarith
