-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.hasDerivAt_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:12.816931+00:00
-- url     : https://prove2.me/submissions/ec74af43-3e70-44df-8d5e-873bdff98e72

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z : V n} (hz : z ∈ Ω) (e : V n) (μ : ℂ) :
    HasDerivAt (fun t : ℝ => F (z + t • (μ • e))) (fderiv ℂ F z e * μ) 0 := by
  have hd : DifferentiableAt ℂ F z := hF.differentiableAt (hΩ.mem_nhds hz)
  have hl : HasDerivAt (fun t : ℝ => z + t • (μ • e)) ((1 : ℝ) • (μ • e)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const (μ • e)).const_add z
  have h1 := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  refine h1.congr_deriv ?_
  rw [one_smul, ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul, mul_comm]
end ReciprocityTheory.L2DbarEstimates.C
