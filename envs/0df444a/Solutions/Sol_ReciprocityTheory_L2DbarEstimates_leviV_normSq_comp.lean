-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.leviV_normSq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:28.967997+00:00
-- url     : https://prove2.me/submissions/54889314-a708-4115-97c6-c309b862911b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_of_differentiableAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_mul
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
theorem _root_.solution {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x ξ =
      ((Complex.normSq (∑ j, wd n j g x * ξ j) : ℝ) : ℂ) := by
  have hcd : ∀ {f : V n → ℂ} {y : V n}, DifferentiableAt ℝ f y →
      DifferentiableAt ℝ (fun z => conj (f z)) y :=
    fun h => Complex.conjCLE.differentiableAt.comp _ h
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℂ 2 g y := hg.eventually (by simp)
  have hdC : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y :=
    hev.mono fun y hy => hy.differentiableAt (by norm_num)
  have hgR : DifferentiableAt ℝ g x := (hg.differentiableAt (by norm_num)).restrictScalars ℝ

  have hwdk : ∀ k, wd n k g =ᶠ[𝓝 x] fun y => fderiv ℂ g y (bas n k) :=
    fun k => hdC.mono fun y hy => wd_of_differentiableAt hy
  have hfd : ∀ k, DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n k)) x := by
    intro k
    have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by norm_num)
    exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  have hwdbwd : ∀ j k, wdb n j (wd n k g) x = 0 :=
    fun j k => (wdb_congr (hwdk k)).trans (wdb_of_differentiableAt (hfd k))
  have hwdR : ∀ k, DifferentiableAt ℝ (wd n k g) x :=
    fun k => ((hfd k).restrictScalars ℝ).congr_of_eventuallyEq (hwdk k)
  have hwdbf : ∀ k, wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => g y * conj (wd n k g y) := by
    intro k
    filter_upwards [hev] with y hy
    have hyC : DifferentiableAt ℂ g y := hy.differentiableAt (by norm_num)
    have hyR : DifferentiableAt ℝ g y := hyC.restrictScalars ℝ
    rw [show (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) from
      funext fun y => (Complex.mul_conj (g y)).symm, wdb_mul hyR (hcd hyR), wdb_conj hyR,
      wdb_of_differentiableAt hyC, zero_mul, zero_add]
  have hterm : ∀ j k, wd n j (wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ))) x =
      wd n j g x * conj (wd n k g x) := by
    intro j k
    rw [wd_congr (hwdbf k), wd_mul hgR (hcd (hwdR k)), wd_conj (hwdR k), hwdbwd j k, map_zero,
      mul_zero, add_zero]
  unfold leviV
  simp_rw [hterm]
  rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]
  ring
end ReciprocityTheory.L2DbarEstimates
