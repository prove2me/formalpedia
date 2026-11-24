-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_contDiff_linEval_b27409562f54
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:15.559167+00:00
-- url     : https://prove2.me/submissions/a79fadb6-bce5-4dc4-bb7c-078d94aa32ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (u : Fin n → ℂ) : ContDiff ℝ ∞ (fun x : Fin n → ℂ => linEval u x) := by
  unfold linEval
  exact ContDiff.sum fun j _ => contDiff_const.mul ((contDiff_apply ℝ ℂ j).restrict_scalars ℝ)
end GroundTheory.Heights₂.Heights
