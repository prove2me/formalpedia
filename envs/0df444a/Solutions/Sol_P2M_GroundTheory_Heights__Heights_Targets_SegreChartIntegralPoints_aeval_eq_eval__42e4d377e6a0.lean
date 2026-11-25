-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_SegreChartIntegralPoints_aeval_eq_eval__42e4d377e6a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:03:31.114913+00:00
-- url     : https://prove2.me/submissions/e1165842-24c2-4446-872d-793f3eefeee5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartIntegralPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPointIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartIntegralPoints
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_segreChartComponents_1a9d50ef3666
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_sameOrbit_of_segre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_smul


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsMultiHomogIdeal ptsIntegral pot segre mcPts SameOrbit
  segre_smul mcPts_smul sameOrbit_of_segre)
open GroundTheory.Heights₂.Heights (varInt IsDegZeroSmooth segreChartSet segreChartComponents segreChartIdeal chartLift
  chartLift_segre_apply mem_segreChartComponents)
open GroundTheory.Heights₂.Heights.Targets.SegreChartIntegralPoints
namespace GroundTheory.Heights₂.Heights.Targets.SegreChartIntegralPoints
theorem _root_.solution {m : ℕ} (x : Fin m → ℂ) (p : MvPolynomial (Fin m) ℂ) : aeval x p = eval x p := rfl
end GroundTheory.Heights₂.Heights.Targets.SegreChartIntegralPoints
