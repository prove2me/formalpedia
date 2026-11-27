-- Prove2me | solution 1 for P2M_GlobalTheory_TopExt_mul__Multi_congr_3a4c7c8aee3c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:53:02.770324+00:00
-- url     : https://prove2.me/submissions/df80a766-d7c9-4f02-8094-db137b8189ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsDetEquivOfSubsingleton
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul



set_option autoImplicit false
open TensorProduct Module Function
open GlobalTheory
open GlobalTheory.TopExt
variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]
namespace GlobalTheory.TopExt
theorem _root_.solution (i : F →ₗ[R] H) {b : ℕ} (x : ExteriorAlgebra R H)
    (hx : ∀ f, x * ExteriorAlgebra.ι R (i f) = 0) (h h' : Fin b → H)
    (hh : ∀ k, h k - h' k ∈ LinearMap.range i) :
    x * ExteriorAlgebra.ιMulti R b h = x * ExteriorAlgebra.ιMulti R b h' := by
  induction b generalizing x with
  | zero => simp
  | succ b ih =>
    obtain ⟨f, hf⟩ := hh 0
    have h0 : x * ExteriorAlgebra.ι R (h 0) = x * ExteriorAlgebra.ι R (h' 0) := by
      rw [← sub_eq_zero, ← mul_sub, ← map_sub, ← hf, hx]
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply, ← mul_assoc,
      ← mul_assoc, h0]
    refine ih _ (fun g => ?_) _ _ fun k => hh k.succ
    rw [mul_assoc, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (h' 0) (i g)),
      mul_neg, ← mul_assoc, hx, zero_mul, neg_zero]
end GlobalTheory.TopExt
