-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_mCoordIdeal_y_e947815fd601
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:05:43.97768+00:00
-- url     : https://prove2.me/submissions/9ba4b682-1f42-488e-bbbf-1748db56a799

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_eval_mConeMap_98a0bb99d678

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
theorem _root_.solution : mCoordIdeal (ι := GlobalTheory (Fin 2)) y = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot]
  have h0 : mConeMap y f = 0 := hf
  have h1 := eval_mConeMap f
  rw [h0, eval₂_zero] at h1
  exact (IsFractionRing.injective (MRing (GlobalTheory (Fin 2))) Kfr) (by rw [← h1, map_zero])
end GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
