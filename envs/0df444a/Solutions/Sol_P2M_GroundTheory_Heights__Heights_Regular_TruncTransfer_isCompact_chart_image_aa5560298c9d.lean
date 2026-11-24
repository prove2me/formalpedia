-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_isCompact_chart_image_aa5560298c9d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:34.04627+00:00
-- url     : https://prove2.me/submissions/6d4e0fdc-0aff-452f-badb-5d39c7fd64f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PTruncTransfer

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
open Metric Filter Topology Set
open ReciprocityTheory.AnForm.A (coordDiv limsupExt polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.TruncTransfer
variable {D : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X] {A : FinHolAtlas D X}
  (R : RegChartData A)
namespace GroundTheory.Heights₂.Heights.Regular.TruncTransfer
theorem _root_.solution (j : Fin R.N) {s : Set X} (hs : s ⊆ closure (R.mid j))
    (hsc : IsClosed s) : IsCompact (R.chart j '' s) :=
  hsc.isCompact.image_of_continuousOn ((R.chart j).continuousOn.mono (hs.trans (R.closure_mid j)))
end GroundTheory.Heights₂.Heights.Regular.TruncTransfer
