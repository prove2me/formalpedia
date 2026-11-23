-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.leviChain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:38.288285+00:00
-- url     : https://prove2.me/submissions/61784c21-8eb5-4b05-b2e3-89e705657e85

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_ofReal_normSq_sum_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_deriv_of_contDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_wdb
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_eventually_differentiableAt_of_contDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_ofReal_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_ofReal_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution : LeviChainStatement := by
  intro n k v x ξ hv hk
  have hv1 : DifferentiableAt ℝ v x := hv.differentiableAt (by simp)
  have hk1 : DifferentiableAt ℝ (deriv k) (v x) := differentiableAt_deriv_of_contDiffAt hk
  have hv' : ContDiffAt ℝ 2 (fun y => ((v y : ℝ) : ℂ)) x :=
    ofRealCLM.contDiff.contDiffAt.comp x hv
  have hvd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y := eventually_differentiableAt_of_contDiffAt hv
  have hkd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ k (v y) :=
    hv1.continuousAt.tendsto.eventually (eventually_differentiableAt_of_contDiffAt hk)
  have hE : ∀ kk : Fin n, wdb n kk (fun y => ((k (v y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => ((deriv k (v y) : ℝ) : ℂ) * wdb n kk (fun y => ((v y : ℝ) : ℂ)) y := by
    intro kk
    filter_upwards [hvd, hkd] with y hy1 hy2
    exact wdb_ofReal_comp hy2 hy1
  have hD1 : DifferentiableAt ℝ (fun y => ((deriv k (v y) : ℝ) : ℂ)) x :=
    differentiableAt_ofReal (hk1.comp x hv1)
  have hterm : ∀ j kk : Fin n, wd n j (wdb n kk (fun y => ((k (v y) : ℝ) : ℂ))) x =
      ((deriv (deriv k) (v x) : ℝ) : ℂ) * wd n j (fun y => ((v y : ℝ) : ℂ)) x *
          conj (wd n kk (fun y => ((v y : ℝ) : ℂ)) x) +
        ((deriv k (v x) : ℝ) : ℂ) * wd n j (wdb n kk (fun y => ((v y : ℝ) : ℂ))) x := by
    intro j kk
    rw [wd_congr (hE kk),
      wd_mul (f := fun y => ((deriv k (v y) : ℝ) : ℂ)) (g := wdb n kk (fun y => ((v y : ℝ) : ℂ)))
        hD1 (differentiableAt_wdb hv'),
      wd_ofReal_comp hk1 hv1, wdb_ofReal hv1]
  rw [ofReal_normSq_sum_mul]
  simp only [leviV, hterm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun kk _ => ?_
  ring
end ReciprocityTheory.L2DbarEstimates
