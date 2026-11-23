-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.leviV_ofReal_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:31.932304+00:00
-- url     : https://prove2.me/submissions/76062d50-fabe-45b0-9b70-73e901b446f7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex ComplexConjugate Filter Topology Matrix
namespace ReciprocityTheory.L2DbarEstimates.H
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
private theorem wd_wdb_finset_sum {m : ℕ} {j : Fin n} {G : Fin m → V n → ℂ} {x : V n}
    (hG : ∀ i, DifferentiableAt ℝ (G i) x) :
    wd n j (fun y => ∑ i, G i y) x = ∑ i, wd n j (G i) x := by
  have hd : ∀ i ∈ Finset.univ, DifferentiableAt ℝ (G i) x := fun i _ => hG i
  unfold wd
  first
  | rw [fderiv_fun_sum hd]
  | rw [fderiv_sum hd]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
private theorem wdb_sum' {m : ℕ} {k : Fin n} {G : Fin m → V n → ℂ} {x : V n}
    (hG : ∀ i, DifferentiableAt ℝ (G i) x) :
    wdb n k (fun y => ∑ i, G i y) x = ∑ i, wdb n k (G i) x := by
  have hd : ∀ i ∈ Finset.univ, DifferentiableAt ℝ (G i) x := fun i _ => hG i
  unfold wdb
  first
  | rw [fderiv_fun_sum hd]
  | rw [fderiv_sum hd]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
private theorem wd_apply_congr_of_eventuallyEq {j : Fin n} {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) :
    wd n j f x = wd n j g x := by
  unfold wd
  rw [h.fderiv_eq]
private theorem wdb_differentiableAt_of_contDiffAt_two {k : Fin n} {U : V n → ℂ} {x : V n} (hU : ContDiffAt ℝ 2 U x) :
    DifferentiableAt ℝ (wdb n k U) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ U) x :=
    hU.fderiv_right (by first | norm_num | rfl | simp)
  have h2 : DifferentiableAt ℝ (fderiv ℝ U) x := h1.differentiableAt one_ne_zero
  unfold wdb
  have h3 : DifferentiableAt ℝ (fun y => fderiv ℝ U y (bas n k)) x :=
    h2.clm_apply (differentiableAt_const _)
  have h4 : DifferentiableAt ℝ (fun y => fderiv ℝ U y (Complex.I • bas n k)) x :=
    h2.clm_apply (differentiableAt_const _)
  have h5 : DifferentiableAt ℝ (fun y => fderiv ℝ U y (bas n k) +
      Complex.I * fderiv ℝ U y (Complex.I • bas n k)) x := h3.add (h4.const_mul Complex.I)
  first
  | fun_prop
  | exact h5.div_const (2 : ℂ)
  | exact (h5.mul_const ((2 : ℂ)⁻¹)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => div_eq_mul_inv _ _)
end ReciprocityTheory.L2DbarEstimates.H
end

set_option autoImplicit false
open Complex ComplexConjugate Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution {m : ℕ} {u : Fin m → V n → ℝ} {x : V n}
    (hu : ∀ i, ContDiffAt ℝ 2 (u i) x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((∑ i, u i y : ℝ) : ℂ)) x ξ = ∑ i, leviV n (fun y => (u i y : ℂ)) x ξ := by
  have hU : ∀ i, ContDiffAt ℝ 2 (fun y => ((u i y : ℝ) : ℂ)) x :=
    fun i => Complex.ofRealCLM.contDiff.contDiffAt.comp x (hu i)
  have hfun : (fun y => ((∑ i, u i y : ℝ) : ℂ)) = fun y => ∑ i, ((u i y : ℝ) : ℂ) := by
    funext y
    exact Complex.ofReal_sum _ _
  have hev : ∀ᶠ y in 𝓝 x, ∀ i, DifferentiableAt ℝ (fun y => ((u i y : ℝ) : ℂ)) y := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [(hU i).eventually (by first | simp | decide | norm_num)] with y hy
    exact hy.differentiableAt (by first | norm_num | simp | exact one_le_two)
  have hwdb : ∀ k, wdb n k (fun y => ∑ i, ((u i y : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => ∑ i, wdb n k (fun y => ((u i y : ℝ) : ℂ)) y := by
    intro k
    filter_upwards [hev] with y hy
    exact wdb_sum' hy
  have hterm : ∀ j k, wd n j (wdb n k (fun y => ((∑ i, u i y : ℝ) : ℂ))) x =
      ∑ i, wd n j (wdb n k (fun y => ((u i y : ℝ) : ℂ))) x := by
    intro j k
    rw [hfun, wd_apply_congr_of_eventuallyEq (hwdb k), wd_wdb_finset_sum fun i => wdb_differentiableAt_of_contDiffAt_two (hU i)]
  unfold leviV
  simp only [hterm, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
end ReciprocityTheory.L2DbarEstimates.H
