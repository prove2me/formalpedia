-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.snd_nonpos_of_isLocalMax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:54:07.186897+00:00
-- url     : https://prove2.me/submissions/50e29e69-cb42-4e20-8555-c5742a599bc8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_deriv_deriv_nonpos_of_isLocalMax
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_eventually_differentiableAt_of_contDiffAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex ComplexConjugate Filter Topology
namespace ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
private theorem differentiableAt_fderiv_of_contDiffAt_two' {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (fderiv ℝ f) x :=
  (hf.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt (by norm_num)
end ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
end

set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
set_option maxHeartbeats 400000
namespace ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
theorem _root_.solution {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) (u : V n) : fderiv ℝ (fderiv ℝ f) x u u ≤ 0 := by
  have hD := differentiableAt_fderiv_of_contDiffAt_two' hf
  have hγd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • u) u t := fun t => by
    simpa using ((hasDerivAt_id' t).smul_const u).const_add x
  have hγ : Tendsto (fun t : ℝ => x + t • u) (𝓝 0) (𝓝 x) := by
    have h := (hγd 0).continuousAt.tendsto
    simpa using h
  have hev := hγ.eventually (ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf)
  have hgd : ∀ t : ℝ, DifferentiableAt ℝ f (x + t • u) →
      HasDerivAt (fun t : ℝ => f (x + t • u)) (fderiv ℝ f (x + t • u) u) t :=
    fun t ht => ht.hasFDerivAt.comp_hasDerivAt t (hγd t)
  have hg : IsLocalMax (fun t : ℝ => f (x + t • u)) 0 := by
    show ∀ᶠ t in 𝓝 (0:ℝ), f (x + t • u) ≤ f (x + (0:ℝ) • u)
    filter_upwards [hγ.eventually (show ∀ᶠ y in 𝓝 x, f y ≤ f x from hmax)] with t ht
    simpa using ht
  have hdg : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ (fun t : ℝ => f (x + t • u)) t := by
    filter_upwards [hev] with t ht using (hgd t ht).differentiableAt
  have hEq : deriv (fun t : ℝ => f (x + t • u)) =ᶠ[𝓝 0] fun t => fderiv ℝ f (x + t • u) u := by
    filter_upwards [hev] with t ht using (hgd t ht).deriv
  have hφ : HasFDerivAt (fun y => fderiv ℝ f y u) ((fderiv ℝ (fderiv ℝ f) x).flip u) (x + (0:ℝ) • u) := by
    rw [zero_smul, add_zero]
    exact (hD.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).congr_fderiv (by ext b; simp)
  have h3 := hφ.comp_hasDerivAt (0:ℝ) (hγd 0)
  have h4 : ((fderiv ℝ (fderiv ℝ f) x).flip u) u = fderiv ℝ (fderiv ℝ f) x u u :=
    ContinuousLinearMap.flip_apply _ _ _
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • u) u) (fderiv ℝ (fderiv ℝ f) x u u) 0 := by
    rw [← h4]
    exact h3
  have h := deriv_deriv_nonpos_of_isLocalMax hg hdg
  rwa [hEq.deriv_eq, h2.deriv] at h
end ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
