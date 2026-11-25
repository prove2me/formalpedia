-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.wd_ofReal_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:33:58.165078+00:00
-- url     : https://prove2.me/submissions/62137aa4-ad52-4b3c-840a-898c84550575

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution {m : ℕ} {j : Fin n} {u : Fin m → V n → ℝ} {x : V n}
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) :
    wd n j (fun y => ((∑ i, u i y : ℝ) : ℂ)) x = ∑ i, wd n j (fun y => (u i y : ℂ)) x := by
  have hfun : (fun y => ((∑ i, u i y : ℝ) : ℂ)) = fun y => ∑ i, ((u i y : ℝ) : ℂ) := by
    funext y
    exact Complex.ofReal_sum _ _
  have hd : ∀ i ∈ Finset.univ, DifferentiableAt ℝ (fun y => ((u i y : ℝ) : ℂ)) x :=
    fun i _ => Complex.ofRealCLM.differentiableAt.comp x (hu i)
  unfold wd
  rw [hfun]
  first
  | rw [fderiv_fun_sum hd]
  | rw [fderiv_sum' hd]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
end ReciprocityTheory.L2DbarEstimates.H
