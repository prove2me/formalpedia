-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:23.637091+00:00
-- url     : https://prove2.me/submissions/eb6e61f3-5c2c-49af-b486-2f06c8338905

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_eventually_differentiableAt_of_contDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_fderiv_ofReal_apply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr

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
private theorem wirtinger_wirtingerBar_ofReal_lemma_2 {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) (j k : Fin n) :
    ReciprocityTheory.L2DbarEstimates.wd n j (ReciprocityTheory.L2DbarEstimates.wdb n k (fun y => (f y : ℂ))) x =
      (((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) +
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) -
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) / 4 := by
  have hD := differentiableAt_fderiv_of_contDiffAt_two' hf
  have hψ : ∀ a : ReciprocityTheory.L2DbarEstimates.V n, HasFDerivAt (fun y => ((fderiv ℝ f y a : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip a)) x := by
    intro a
    have h1 : HasFDerivAt (fun y => fderiv ℝ f y a) ((fderiv ℝ (fderiv ℝ f) x).flip a) x :=
      (hD.hasFDerivAt.clm_apply (hasFDerivAt_const a x)).congr_fderiv (by ext b; simp)
    exact (Complex.ofRealCLM.hasFDerivAt.comp x h1).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp)
  have hG : HasFDerivAt (fun y => (2⁻¹ : ℂ) * (((fderiv ℝ f y (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ f y (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)))
      ((2⁻¹ : ℂ) • (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip (ReciprocityTheory.L2DbarEstimates.bas n k)) +
        I • Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip (I • ReciprocityTheory.L2DbarEstimates.bas n k)))) x :=
    ((hψ (ReciprocityTheory.L2DbarEstimates.bas n k)).add ((hψ (I • ReciprocityTheory.L2DbarEstimates.bas n k)).const_mul I)).const_mul (2⁻¹ : ℂ)
  have hE : ReciprocityTheory.L2DbarEstimates.wdb n k (fun y => (f y : ℂ)) =ᶠ[𝓝 x] fun y =>
      (2⁻¹ : ℂ) * (((fderiv ℝ f y (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ f y (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) := by
    filter_upwards [ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf] with y hy
    rw [ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy, div_eq_inv_mul]
  rw [ReciprocityTheory.L2DbarEstimates.wd_congr hE, ReciprocityTheory.L2DbarEstimates.wd, hG.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  push_cast
  linear_combination
    (-((fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) / 4) * I_sq
private theorem euclideanLeviForm_ofReal_eq_lemma_3 {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) (ξ : Fin n → ℂ) :
    ReciprocityTheory.L2DbarEstimates.leviV n (fun y => (f y : ℂ)) x ξ =
      ∑ j, ∑ k, (((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) +
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) -
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) / 4 *
          ξ j * conj (ξ k) := by
  simp only [ReciprocityTheory.L2DbarEstimates.leviV, wirtinger_wirtingerBar_ofReal_lemma_2 hf]
end ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
end

set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
theorem _root_.solution {f g : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((f y + g y : ℝ) : ℂ)) x ξ =
      leviV n (fun y => (f y : ℂ)) x ξ + leviV n (fun y => (g y : ℂ)) x ξ := by
  have hfg : ContDiffAt ℝ 2 (fun y => f y + g y) x := hf.add hg
  have hT : fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
    have hev : fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 x] fun y => fderiv ℝ f y + fderiv ℝ g y := by
      filter_upwards [ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf,
        ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hg] with y hfy hgy
      exact fderiv_add hfy hgy
    rw [hev.fderiv_eq]
    exact fderiv_add (differentiableAt_fderiv_of_contDiffAt_two' hf)
      (differentiableAt_fderiv_of_contDiffAt_two' hg)
  rw [euclideanLeviForm_ofReal_eq_lemma_3 hfg, euclideanLeviForm_ofReal_eq_lemma_3 hf, euclideanLeviForm_ofReal_eq_lemma_3 hg, hT]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ContinuousLinearMap.add_apply]
  push_cast
  ring
end ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
