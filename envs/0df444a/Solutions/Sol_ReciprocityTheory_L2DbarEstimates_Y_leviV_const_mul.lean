-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:41:33.944158+00:00
-- url     : https://prove2.me/submissions/762ee811-2b50-4c19-abb4-2f7629b69da7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviChain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (c d : ℝ)
    (ξ : Fin n → ℂ) :
    leviV n (fun y => ((c * f y + d : ℝ) : ℂ)) x ξ = c * leviV n (fun y => ((f y : ℝ) : ℂ)) x ξ := by
  have hk : ContDiffAt ℝ 2 (fun t : ℝ => c * t + d) (f x) :=
    ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)
  have h := leviChain n (fun t : ℝ => c * t + d) f x ξ hf hk
  have hd : deriv (fun t : ℝ => c * t + d) = fun _ => c := by
    funext t; rw [deriv_add_const, deriv_const_mul_field', deriv_id'']; ring
  rw [h, hd]; simp
end ReciprocityTheory.L2DbarEstimates.Y
