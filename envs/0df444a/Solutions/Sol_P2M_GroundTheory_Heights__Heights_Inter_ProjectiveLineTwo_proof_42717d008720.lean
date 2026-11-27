-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ProjectiveLineTwo_proof_42717d008720
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:00:36.374237+00:00
-- url     : https://prove2.me/submissions/e00a393a-8b16-405e-89d4-ec0560a023de

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_DeEqZeroOfSemiPosOff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_De_eq_zero_of_semiPos_off_f1c76f1ce662

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {n : ℕ}
  {A A' : HermLine ι} {s s' : MRing ι}
namespace GroundTheory.Heights₂.Heights.Inter
namespace ProjectiveLineTwo
theorem _root_.solution (hAdd : DeSlotAdd.Statement) (hTw : SemiPosTwist.Statement)
    (hLe : DeLeSemiPos.Statement) : SectionSpaceSymmetry := by
  intro K _ ι _ P n L A A' s s' hP hL hA hA' hs hs' hnc
  have h := De_eq_zero_of_semiPos_off hAdd hTw hLe hP hA hA' hs hs' hnc Finset.univ L hL
    (fun j hj => absurd (Finset.mem_univ j) hj)
  unfold De at h
  linarith
end ProjectiveLineTwo
end GroundTheory.Heights₂.Heights.Inter
