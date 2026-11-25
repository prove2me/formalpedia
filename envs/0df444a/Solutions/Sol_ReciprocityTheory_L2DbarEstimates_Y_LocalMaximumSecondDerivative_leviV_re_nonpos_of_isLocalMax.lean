-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:09:44.650285+00:00
-- url     : https://prove2.me/submissions/a4cd0550-60b6-4a2a-810b-89d6a2be23f0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_snd_nonpos_of_isLocalMax
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_re_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
theorem _root_.solution {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) (ξ : Fin n → ℂ) : (leviV n (fun y => (f y : ℂ)) x ξ).re ≤ 0 := by
  have h := leviV_re_eq hf ξ
  have h1 := snd_nonpos_of_isLocalMax hf hmax
    (∑ k, ((ξ k).re • ReciprocityTheory.L2DbarEstimates.bas n k + (ξ k).im • (I • ReciprocityTheory.L2DbarEstimates.bas n k)))
  have h2 := snd_nonpos_of_isLocalMax hf hmax
    (∑ k, ((ξ k).re • (I • ReciprocityTheory.L2DbarEstimates.bas n k) - (ξ k).im • ReciprocityTheory.L2DbarEstimates.bas n k))
  linarith
end ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
