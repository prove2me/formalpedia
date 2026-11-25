-- Prove2me | solution 1 for P2M_GlobalTheory_ValCompletion_isUnit_of_eval__93ec6f237660
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:31.727035+00:00
-- url     : https://prove2.me/submissions/1bd04c74-bfe8-4755-8200-ccc1262b64ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionValuationRingCompleteValuationDoma
import Theorems.Thm_P2M_GlobalTheory_ValCompletion_factorPow_eval__29f3d9d0163b
import Theorems.Thm_P2M_GlobalTheory_ValCompletion_isUnit_eval__7091914be88c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory GlobalTheory.ValCompletion
variable {R : Type} [CommRing R] {I : Ideal R} {a : R}
namespace GlobalTheory.ValCompletion
theorem _root_.solution (y : AdicCompletion I R) (hy : IsUnit (AdicCompletion.evalₐ I 1 y)) :
    IsUnit y := by
  let f : (n : ℕ) → Localization.Away y →+* R ⧸ I ^ n := fun n =>
    IsLocalization.Away.lift (g := (AdicCompletion.evalₐ I n).toRingHom) y (isUnit_evalₐ y hy n)
  have hf0 : ∀ n x, f n (algebraMap _ _ x) = AdicCompletion.evalₐ I n x := fun n x =>
    IsLocalization.Away.lift_eq y _ x
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
    intro m n hle
    refine IsLocalization.ringHom_ext (Submonoid.powers y) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, hf0, factorPow_evalₐ]
  have e : AdicCompletion.liftRingHom I f hf (algebraMap _ _ y) = y :=
    AdicCompletion.ext_evalₐ fun n => by rw [AdicCompletion.evalₐ_liftRingHom, hf0]
  rw [← e]
  exact (IsLocalization.Away.algebraMap_isUnit y).map _
end GlobalTheory.ValCompletion
