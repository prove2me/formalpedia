-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_norm_eval_curveChartMono_08314128b296
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:21:06.951993+00:00
-- url     : https://prove2.me/submissions/3bac6de7-c2fc-44a1-90b8-7443e2766427

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveDegreeVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveDegreeVert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveDegreeVert
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.CurveDegreeVert
theorem _root_.solution (c : ∀ k, ι k) (e : K → ℕ) (z : (Σ k, ι k) → ℂ) :
    ‖eval z (map (Int.castRingHom ℂ) (curveChartMono c e))‖ = ∏ k, ‖z ⟨k, c k⟩‖ ^ e k := by
  simp [curveChartMono, map_prod, norm_prod]
end GroundTheory.Heights₂.Heights.Targets.CurveDegreeVert
