-- Prove2me | solution 1 for P2M_GlobalTheory_AdicQuot_eval__psi_3e690848319d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:43.889872+00:00
-- url     : https://prove2.me/submissions/b9f1713c-8329-4b8e-9a03-54c3cf2922fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.AdicQuot
open AdicCompletion
variable {A : Type} [CommRing A] (J q : Ideal A)
namespace GlobalTheory.AdicQuot
theorem _root_.solution (n : ℕ) (x : AdicCompletion J A) :
    evalₐ _ n (psi J q x) = lev J q n x := by
  simp [psi]
end GlobalTheory.AdicQuot
