-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_isSectionBounded_one_0265e525520e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:31:53.123218+00:00
-- url     : https://prove2.me/submissions/057da1bc-56ba-4a01-8325-431cf03e57f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_eval__homog_pt_f24e64e8269f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_fsLine_one_h_b1e1fdfc0ffb

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open NumberField
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
theorem _root_.solution :
    IsSectionBounded (mCoordIdeal (ι := PBlk 1) yPt) yPt (fsLine 1) 1 (Real.exp 0) := by
  intro dg dh g h z hg hh hd hgh _
  have hd' : dg () = dh () + 1 := by
    have := hd ()
    simp only [fsLine, HermLine.ofMetrics, Pi.one_apply] at this
    omega
  rw [aeval_def, aeval_def, eval₂_homog_pt _ _ g dg hg, eval₂_homog_pt _ _ h dh hh] at hgh
  simp only [yPt, one_pow, mul_one, one_mul, algebraMap_int_eq, eq_intCast, Int.cast_inj] at hgh
  rw [eval_map, eval_map, eval₂_homog_pt _ _ g dg hg, eval₂_homog_pt _ _ h dh hh, hgh, hd',
    fsLine_one_h, Real.exp_zero, one_mul, pow_succ, ← mul_assoc, norm_mul (_ * _)]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
