-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.Chart.mat_expG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:23.134294+00:00
-- url     : https://prove2.me/submissions/ee397a62-7ecf-4596-8add-1b63c37ff0cd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open ReciprocityTheory.ChartRestriction.DS.HExp.Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)
namespace ReciprocityTheory.ChartRestriction.DS.HExp.Chart
theorem _root_.solution (X : V) : C.mat (C.expG X) = exp (X : 𝔸) := (C.H1 X).choose_spec
end ReciprocityTheory.ChartRestriction.DS.HExp.Chart
