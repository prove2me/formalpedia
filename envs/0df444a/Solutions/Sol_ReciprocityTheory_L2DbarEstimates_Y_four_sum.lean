-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.four_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:51:36.163155+00:00
-- url     : https://prove2.me/submissions/0258cba7-5435-4e11-b903-63bb0252ddbd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fsFun_proj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fsFun_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fs_mFourier_proj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (f : ℕ) : FOURSumStatement f := by
  intro Ω h hΩ hh hper h0 hsum x
  set g : (Fin f → ℝ) → ℂ := fun x => h (fun k => (x k : ℂ)) with hgdef
  have hreal : ∀ y : Fin f → ℝ, (fun k => ((y k : ℝ) : ℂ)) ∈ tube f Ω := by
    intro y
    show (fun k => ((y k : ℝ) : ℂ).im) ∈ Ω
    have e : (fun k => (((y k : ℝ) : ℂ)).im) = 0 := by funext k; simp
    rw [e]; exact h0
  have hg : Continuous g := by
    have hc : Continuous (fun y : Fin f → ℝ => (fun k => ((y k : ℝ) : ℂ))) := by fun_prop
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hopen : IsOpen (tube f Ω) := hΩ.preimage (by fun_prop)
    exact ((hh _ (hreal y)).differentiableAt (hopen.mem_nhds (hreal y))).continuousAt.comp
      hc.continuousAt
  have hgper : ∀ x (n : Fin f → ℤ), g (x + fun i => (n i : ℝ)) = g x := by
    intro y n
    have := hper _ (hreal y) n
    simp only [hgdef]
    convert this using 2
    funext k
    simp
  let F : C(UnitAddTorus (Fin f), ℂ) := ⟨fsFun g, fsFun_continuous g hg hgper⟩
  have hcoef : ∀ ν, UnitAddTorus.mFourierCoeff F ν = fourCoeff h 0 ν := by
    intro ν
    rw [UnitAddTorus.mFourierCoeff_eq_integral _ ν 0, fourCoeff]
    have hset : ({x : Fin f → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin f → ℝ) i) ((0 : Fin f → ℝ) i + 1)}
        : Set (Fin f → ℝ)) = Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1) := by
      ext x; simp
    rw [hset]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have h1 : (fun i => ((t i : ℝ) : UnitAddCircle)) = fsProj f t := rfl
    have h2 : F (fsProj f t) = g t := fsFun_proj g hgper t
    beta_reduce
    rw [h1, h2, smul_eq_mul, fs_mFourier_proj]
    simp only [hgdef, Pi.zero_apply, Complex.ofReal_zero, zero_mul, add_zero, Pi.neg_apply, Int.cast_neg]
    rw [mul_comm]
    congr 2
    simp [Finset.sum_neg_distrib]
  have hs : Summable (UnitAddTorus.mFourierCoeff F) := by
    refine Summable.of_norm ?_
    simpa [hcoef] using hsum
  have := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (fsProj f x)
  simp only [hcoef, smul_eq_mul, fs_mFourier_proj] at this
  rw [show F (fsProj f x) = g x from fsFun_proj g hgper x] at this
  exact this
end ReciprocityTheory.L2DbarEstimates.Y
