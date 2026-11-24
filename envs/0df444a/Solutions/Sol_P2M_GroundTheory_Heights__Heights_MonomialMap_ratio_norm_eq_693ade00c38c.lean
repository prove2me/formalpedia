-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMap_ratio_norm_eq_693ade00c38c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:21.565906+00:00
-- url     : https://prove2.me/submissions/642d336c-6de2-4ea3-aee1-7b4ecb9fd93b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroAlt

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
open GroundTheory.Heights₂.Heights.MonomialMap
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.MonomialMap
theorem _root_.solution {e e' x x' : ℂ} (hx : x ≠ 0) (hx' : x' ≠ 0) (h : e * x' = e' * x) (M : ℝ) :
    ‖e‖ / (‖x‖ * M) = ‖e'‖ / (‖x'‖ * M) := by
  rw [← div_div, ← div_div, ← norm_div, ← norm_div, (div_eq_div_iff hx hx').mpr h]
end GroundTheory.Heights₂.Heights.MonomialMap
