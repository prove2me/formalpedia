-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsCutoff_measurableSet_outer_6bc779b06f82
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:56.258505+00:00
-- url     : https://prove2.me/submissions/c6f26e5f-1936-421b-a1fe-37dbcddc3f8e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartIbpCutoff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open ChartIntegrationByPartsSymmetry
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntegrationByPartsCutoff
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartIntegrationByPartsCutoff
theorem _root_.solution (k : ℕ) : MeasurableSet (outer n k) :=
  (isClosed_le continuous_const (continuous_finsetSum _ fun i _ =>
    (continuous_norm.comp (continuous_apply i)).pow 2)).measurableSet
end GroundTheory.Heights₂.Heights.ChartIntegrationByPartsCutoff
