-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_isCompact_image_closure_mid_4db7e722a909
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:33.433974+00:00
-- url     : https://prove2.me/submissions/8288c297-175e-4b30-80c6-c1129c797b74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsCompactImageClosureMid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli shrink regMax tmax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open ReciprocityTheory.AnForm (levi)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.PotentialCharts
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)
namespace GroundTheory.Heights₂.Heights.Regular.PotentialCharts
theorem _root_.solution [CompactSpace X] (j : Fin P.N) :
    IsCompact ((P.chart j) '' closure (P.mid j)) :=
  isClosed_closure.isCompact.image_of_continuousOn
    ((P.chart j).continuousOn.mono (P.closure_mid j))
end GroundTheory.Heights₂.Heights.Regular.PotentialCharts
