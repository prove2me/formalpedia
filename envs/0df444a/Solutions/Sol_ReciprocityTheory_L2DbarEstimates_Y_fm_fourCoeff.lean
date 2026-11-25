-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fm_fourCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:12:36.995211+00:00
-- url     : https://prove2.me/submissions/87650e69-a627-46e7-88d2-60fa5f957a44

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fsFun_proj
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
open MeasureTheory Filter Topology
open scoped ComplexConjugate
noncomputable section
attribute [local instance] ReciprocityTheory.L2DbarEstimates.Y._p2m_local_instance_19aabe418c_38
attribute [local instance] ReciprocityTheory.L2DbarEstimates.Y._p2m_local_instance_19aabe418c_40
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {f : ℕ} (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ)
    (hper : ∀ x (n : Fin f → ℤ), fmLine h b (x + fun i => (n i : ℝ)) = fmLine h b x)
    (ν : Fin f → ℤ) :
    fourCoeff h b ν = Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)) *
      UnitAddTorus.mFourierCoeff (fsFun (fmLine h b)) ν := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ ν 0, fourCoeff]
  have hset : ({x : Fin f → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin f → ℝ) i) ((0 : Fin f → ℝ) i + 1)}
      : Set (Fin f → ℝ)) = Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1) := by
    ext x; simp
  rw [hset, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have h1 : (fun i => ((t i : ℝ) : UnitAddCircle)) = fsProj f t := rfl
  beta_reduce
  rw [h1, fsFun_proj _ hper, smul_eq_mul, fs_mFourier_proj]
  simp only [fmLine]
  rw [mul_comm, ← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [Pi.neg_apply, Int.cast_neg, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  linear_combination (-2 * (Real.pi : ℂ) * (ν k : ℂ) * (b k : ℂ)) * Complex.I_sq
end ReciprocityTheory.L2DbarEstimates.Y
