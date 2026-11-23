-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.leviV_ofReal_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:37.173908+00:00
-- url     : https://prove2.me/submissions/bbb416a0-5758-49d8-8d01-e960693df934

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_wdb
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_eventually_differentiableAt_of_contDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_sum


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
theorem _root_.solution {m : ℕ} {u : Fin m → V n → ℝ} {x : V n}
    (hu : ∀ i, ContDiffAt ℝ 2 (u i) x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((∑ i, u i y : ℝ) : ℂ)) x ξ = ∑ i, leviV n (fun y => (u i y : ℂ)) x ξ := by
  have hf : (fun y => ((∑ i, u i y : ℝ) : ℂ)) = fun y => ∑ i, (u i y : ℂ) := by
    funext y; push_cast; rfl
  have hc : ∀ i, ContDiffAt ℝ 2 (fun y => (u i y : ℂ)) x := fun i =>
    ofRealCLM.contDiff.contDiffAt.comp x (hu i)
  have hev : ∀ kk : Fin n, wdb n kk (fun y => ∑ i, (u i y : ℂ)) =ᶠ[𝓝 x]
      fun y => ∑ i, wdb n kk (fun y => (u i y : ℂ)) y := by
    intro kk
    have : ∀ᶠ y in 𝓝 x, ∀ i, DifferentiableAt ℝ (fun y => (u i y : ℂ)) y := by
      rw [Filter.eventually_all]; exact fun i => eventually_differentiableAt_of_contDiffAt (hc i)
    filter_upwards [this] with y hy
    exact wdb_sum Finset.univ (fun i _ => hy i)
  rw [hf]
  simp only [leviV, wd_congr (hev _),
    wd_sum Finset.univ (fun i _ => differentiableAt_wdb (hc i)), Finset.sum_mul]
  exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
end ReciprocityTheory.L2DbarEstimates
