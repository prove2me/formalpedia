-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedCech_hEquiv_mk_ddf70a59c8c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:38:52.43107+00:00
-- url     : https://prove2.me/submissions/626d7844-17b1-4770-b03a-c74afb4c0d22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqCech

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech
variable (S : Type) [CommRing S] (N : ℕ)
variable (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {S N M}
variable (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ)
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech
theorem _root_.solution (i : ℕ) (w : IndefiniteRowSideFullHecke.Kleiman.gradedZ S N M G i c) :
    hEquiv G c i (Submodule.Quotient.mk w) = Submodule.Quotient.mk (zEquiv G c i w) := rfl
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech
