-- Prove2me | solution 1 for P2M_GlobalTheory_ValCompletion_factorPow_eval__29f3d9d0163b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:49.415397+00:00
-- url     : https://prove2.me/submissions/62c720f1-b432-479c-9083-cd4d71c6d095

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionValuationRingCompleteValuationDoma

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
theorem _root_.solution {m n : ℕ} (h : m ≤ n) (y : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n y) = AdicCompletion.evalₐ I m y := by
  induction y using AdicCompletion.induction_on with
  | _ x =>
    simp only [AdicCompletion.evalₐ_mk]
    rw [← AdicCompletion.Ideal.mk_eq_mk I h x]
    rfl
end GlobalTheory.ValCompletion
