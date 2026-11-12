-- Prove2me | solution 1 for RLCDiscrepancy.lemma_4_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:13:19.865659+00:00
-- url     : https://prove2.me/submissions/0448c4a0-eccf-47b1-a572-1d7395a04b9e

import Mathlib
import Definitions.Def_RLCDiscrepancy_transl
import Definitions.Def_RLCDiscrepancy_selfConv

section
set_option autoImplicit false
namespace RLCDiscrepancy
theorem chk_lemma_4_11 {F : Type*} [Field F] [Fintype F] {n : ℕ} (f : (Fin n → F) → ℝ)
    (z : Fin n → F) : selfConv (transl f z) = selfConv f := by
  funext w
  unfold selfConv transl
  congr 1
  refine Fintype.sum_equiv (Equiv.addRight z) _ _ ?_
  intro x
  simp only [Equiv.coe_addRight]
  congr 2
  abel
end RLCDiscrepancy
end

theorem solution : type_of% @RLCDiscrepancy.chk_lemma_4_11 := @RLCDiscrepancy.chk_lemma_4_11
