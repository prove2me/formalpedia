-- Prove2me | solution 1 for WagerFairDiv.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:10:41.538523+00:00
-- url     : https://prove2.me/submissions/78bc220d-fad4-4408-9d5a-f9d52845c367

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

open WagerFairDiv in
theorem solution {n m : ℕ} (A B : WagerFairDiv.Mech n m) (hAB : WagerFairDiv.Corresponding A B) :
    (WagerFairDiv.AllocWeakIC A ↔ WagerFairDiv.WagerWeakIC B) ∧
      (WagerFairDiv.AllocStrictIC A ↔ WagerFairDiv.WagerStrictIC B) := by
  have hv : ∀ (q : stdSimplex ℝ (Fin m)) (p : WagerFairDiv.Profile n m) (w : WagerFairDiv.PosVec n)
      (i : Fin n), WagerFairDiv.val q.1 (B p w i) = w.total * WagerFairDiv.val q.1 (A p w i) := by
    intro q p w i
    unfold WagerFairDiv.val
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hAB]
    ring
  have htot : ∀ (w : WagerFairDiv.PosVec n) (i : Fin n), 0 < w.total := by
    intro w i
    unfold WagerFairDiv.PosVec.total
    exact Finset.sum_pos (fun k _ => w.2 k) ⟨i, Finset.mem_univ _⟩
  have weak : WagerFairDiv.AllocWeakIC A ↔ WagerFairDiv.WagerWeakIC B := by
    constructor
    · intro h i pi p w
      rw [hv, hv]
      exact mul_le_mul_of_nonneg_left (h i pi p w) (htot w i).le
    · intro h i vi v e
      have := h i vi v e
      rw [hv, hv] at this
      exact le_of_mul_le_mul_left this (htot e i)
  refine ⟨weak, ?_⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨weak.1 h1, fun i pi p w hne => ?_⟩
    rw [hv, hv]
    exact mul_lt_mul_of_pos_left (h2 i pi p w hne) (htot w i)
  · rintro ⟨h1, h2⟩
    refine ⟨weak.2 h1, fun i vi v e hne => ?_⟩
    have := h2 i vi v e hne
    rw [hv, hv] at this
    exact lt_of_mul_lt_mul_left this (htot e i).le
