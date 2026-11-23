-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flA_wdb_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:18.777252+00:00
-- url     : https://prove2.me/submissions/8ac85a0a-3add-49bc-85bc-402c5c4ed6a1

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_I_pow_three_eq_neg_I
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flA_decomp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flA_fderiv_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (k : Fin n) :
    wdb n k (U ∘ G) y = ∑ b, wdb n b U (G y) * conj (fderiv ℂ G y (bas n k) b) := by
  simp only [wdb]
  rw [flA_fderiv_comp hU hG, flA_fderiv_comp hU hG, map_smul,
    flA_decomp (fderiv ℝ U (G y)) (fderiv ℂ G y (bas n k)),
    flA_decomp (fderiv ℝ U (G y)) (I • fderiv ℂ G y (bas n k))]
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring_nf; simp only [I_sq, I_pow_three_eq_neg_I]; ring_nf
end ReciprocityTheory.L2DbarEstimates.Y
