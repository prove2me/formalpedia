-- Prove2me | solution 1 for P2M_GlobalTheory_ValCompletion_eval__algebraMap_9fca5057166d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:08.092806+00:00
-- url     : https://prove2.me/submissions/8a98ae9d-cbbd-46a1-af33-76a7dc1e0701

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
theorem _root_.solution (n : ℕ) (r : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r) = Ideal.Quotient.mk _ r := by
  rw [AlgHom.commutes]; rfl
end GlobalTheory.ValCompletion
