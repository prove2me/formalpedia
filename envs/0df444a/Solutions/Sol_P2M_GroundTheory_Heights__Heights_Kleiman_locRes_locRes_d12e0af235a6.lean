-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locRes_locRes_d12e0af235a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:51.417731+00:00
-- url     : https://prove2.me/submissions/c846ced5-0099-4271-bc7a-26018a59623c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type*} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {I J K : Finset (Fin (N + 1))} (h1 : I ⊆ J) (h2 : J ⊆ K) (x : LocMod S N M I) :
    locRes h2 (locRes h1 x) = locRes (h1.trans h2) x := by
  revert x
  refine LocalizedModule.induction_on ?_
  intro m s
  rw [locRes_mk, locRes_mk, locRes_mk]
end GroundTheory.Heights₂.Heights.Kleiman
