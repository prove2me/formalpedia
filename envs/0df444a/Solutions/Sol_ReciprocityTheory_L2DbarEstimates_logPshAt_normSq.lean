-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.logPshAt_normSq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:37.910536+00:00
-- url     : https://prove2.me/submissions/ec2ac1ec-edea-40ae-aec4-c7d28f9975cb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_ofReal_normSq_sum_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_of_differentiableAt
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
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    LogPshAt n (fun y => Complex.normSq (g y)) x := by
  have hgR : ContDiffAt ℝ 2 g x := hg.restrict_scalars ℝ
  have hgd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y :=
    (hg.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by simp)
  have hgx : DifferentiableAt ℂ g x := hg.differentiableAt (by simp)
  have hf : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) := by
    funext y; rw [mul_conj]

  have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by norm_num)
  have hh : ∀ kk : Fin n, DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n kk)) x := fun kk =>
    (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
  have hE : ∀ kk : Fin n, wdb n kk (fun y => g y * conj (g y)) =ᶠ[𝓝 x]
      fun y => g y * conj (fderiv ℂ g y (bas n kk)) := by
    intro kk
    filter_upwards [hgd] with y hy
    rw [wdb_mul (hy.restrictScalars ℝ) (differentiableAt_conj (hy.restrictScalars ℝ)),
      wdb_of_differentiableAt hy,
      wdb_conj (hy.restrictScalars ℝ), wd_of_differentiableAt hy]
    ring
  have hterm : ∀ j kk : Fin n, wd n j (wdb n kk (fun y => g y * conj (g y))) x =
      wd n j g x * conj (wd n kk g x) := by
    intro j kk
    rw [wd_congr (hE kk), wd_mul (f := g) (g := fun y => conj (fderiv ℂ g y (bas n kk)))
      (hgx.restrictScalars ℝ) (differentiableAt_conj ((hh kk).restrictScalars ℝ)),
      wd_conj ((hh kk).restrictScalars ℝ), wdb_of_differentiableAt (hh kk)]
    simp [wd_of_differentiableAt hgx]
  have hwd : ∀ j : Fin n, wd n j (fun y => g y * conj (g y)) x = wd n j g x * conj (g x) := by
    intro j
    rw [wd_mul (hgx.restrictScalars ℝ) (differentiableAt_conj (hgx.restrictScalars ℝ)),
      wd_conj (hgx.restrictScalars ℝ),
      wdb_of_differentiableAt hgx]
    simp
  refine ⟨Complex.normSq_nonneg _, fun ξ => ?_⟩
  have hlevi : leviV n (fun y => g y * conj (g y)) x ξ =
      ((Complex.normSq (∑ j, wd n j g x * ξ j) : ℝ) : ℂ) := by
    rw [ofReal_normSq_sum_mul]
    simp only [leviV, hterm]
  rw [hf, hlevi, ofReal_re]
  simp only [hwd]
  have : ∑ j, wd n j g x * conj (g x) * ξ j = conj (g x) * ∑ j, wd n j g x * ξ j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, normSq_mul, normSq_conj]
  exact ⟨Complex.normSq_nonneg _, le_rfl⟩
end ReciprocityTheory.L2DbarEstimates
