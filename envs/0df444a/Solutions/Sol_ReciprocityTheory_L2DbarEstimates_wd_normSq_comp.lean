-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.wd_normSq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:29.139956+00:00
-- url     : https://prove2.me/submissions/f53695e2-917e-480d-b2d0-362df93904ed

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_of_differentiableAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {j : Fin n} {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    wd n j (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x = wd n j g x * conj (g x) := by
  have hgC : DifferentiableAt ℂ g x := hg.differentiableAt (by norm_num)
  have hgR : DifferentiableAt ℝ g x := hgC.restrictScalars ℝ
  have hc : DifferentiableAt ℝ (fun y => conj (g y)) x := Complex.conjCLE.differentiableAt.comp x hgR
  rw [show (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) from
    funext fun y => (Complex.mul_conj (g y)).symm, wd_mul hgR hc, wd_conj hgR,
    wdb_of_differentiableAt hgC, map_zero, mul_zero, add_zero]
end ReciprocityTheory.L2DbarEstimates
