-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.hs_contVG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:05.131344+00:00
-- url     : https://prove2.me/submissions/63f4f478-ae0a-4c96-b952-24cb33034d22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution : Continuous (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (continuous_id.matrix_elem i j).norm.pow 2
end ReciprocityTheory.ChartRestriction.DS.S7
