-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_add_31144b20e51b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:23.475826+00:00
-- url     : https://prove2.me/submissions/11f48c9f-ca17-4a43-878f-6179f54f1ff2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExistsFormOfMemChartRing

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartFormsAlt
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.ChartFormsAlt
theorem _root_.solution (c : (k : ι) → Fin (n k + 1)) (e e' : ι → ℕ) :
    chartMonomial c (e + e') = chartMonomial c e * chartMonomial c e' := by
  simp [chartMonomial, pow_add, Finset.prod_mul_distrib]
end GroundTheory.Heights₂.Heights.ChartFormsAlt
