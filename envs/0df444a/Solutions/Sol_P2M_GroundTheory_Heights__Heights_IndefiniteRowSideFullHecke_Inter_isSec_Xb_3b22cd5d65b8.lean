-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_Xb_3b22cd5d65b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:32:15.014211+00:00
-- url     : https://prove2.me/submissions/0d3c0b1f-06f9-45c7-92db-4fc9ec5b19aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isMultiHomog_Xb_39cccc678346

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (n : ℕ) (i : Fin (n + 1)) : IsSec (⊥ : Ideal (MRing (GlobalTheory (n + 1)))) (fsO1 (n + 1)) (Xb (n + 1) i) :=
  ⟨fun _ => 1, isMultiHomog_Xb _ _, fun _ => by simp [fsO1, HermLine.sqMetric],
    by rw [Ideal.mem_bot]; exact X_ne_zero _⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
