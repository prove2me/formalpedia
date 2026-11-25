-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.hsRV_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:22.948425+00:00
-- url     : https://prove2.me/submissions/33e69653-27e3-4680-bd8b-c2ccd4ad80ab

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
theorem _root_.solution {Q : Type} [Fintype Q] : Continuous (hsRV : Matrix (Fin n) Q ℂ → ℝ) := by
  unfold hsRV
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (continuous_id.matrix_elem i j).norm.pow 2
end ReciprocityTheory.ChartRestriction.DS.S7
