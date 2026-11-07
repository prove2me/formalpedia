-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_coeff_square_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:17:07.061694+00:00
-- url     : https://prove2.me/submissions/2ef4c2d5-d851-4a4f-96ad-f5d07125e859

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_parseval_nat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycle_weighted_square_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycle_weight_exp
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃ C : ℝ, 0≤C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.range X, ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2)≤
        C*(X:ℝ)^2 := by
  obtain ⟨C,hC,hb⟩ := lpsCuspHorocycle_weighted_square_bound N f
  refine ⟨Real.exp (4*Real.pi)*C^2,by positivity,fun X => ?_⟩
  by_cases hx : X=0
  · subst X
    simp
  have hxR : 0<(X:ℝ) := by exact_mod_cast (by omega : 0<X)
  let y : ℝ := 1/(X:ℝ)
  have hy : 0<y := by dsimp [y];positivity
  have hw (n : ℕ) (hn : n∈Finset.range X) :
      Real.exp (-4*Real.pi)≤(Real.exp (-2*Real.pi*y))^(2*n) := by
    rw [lpsCuspHorocycle_weight_exp]
    apply Real.exp_le_exp.mpr
    dsimp [y]
    rw [mul_one_div]
    apply (le_div_iff₀ hxR).mpr
    have hnR : (n:ℝ)≤(X:ℝ) := by exact_mod_cast (Finset.mem_range.mp hn).le
    have h := mul_le_mul_of_nonneg_left hnR (by positivity : 0≤4*Real.pi)
    nlinarith
  have hs : Real.exp (-4*Real.pi)*
      (∑ n ∈ Finset.range X, ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2)≤
      (C/y)^2 := by
    calc
      _ = ∑ n ∈ Finset.range X, Real.exp (-4*Real.pi)*
            ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2 := Finset.mul_sum ..
      _ ≤ ∑ n ∈ Finset.range X, ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
            (Real.exp (-2*Real.pi*y))^(2*n) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [mul_comm (Real.exp _)]
        exact mul_le_mul_of_nonneg_left (hw n hn) (sq_nonneg _)
      _ ≤ ∑' n : ℕ, ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
            (Real.exp (-2*Real.pi*y))^(2*n) :=
        sum_le_hasSum _ (fun n hn => by positivity)
          (lpsCuspHorocycleCircle_parseval_nat N f y hy).summable.hasSum
      _ ≤ _ := hb y hy
  have he : Real.exp (4*Real.pi)*Real.exp (-4*Real.pi)=1 := by
    rw [←Real.exp_add];simp
  have ht := mul_le_mul_of_nonneg_left hs (Real.exp_pos (4*Real.pi)).le
  rw [←mul_assoc,he,one_mul] at ht
  have hd : C/y=C*(X:ℝ) := by dsimp [y];field_simp
  rw [hd,mul_pow] at ht
  simpa only [mul_assoc] using ht
end QEC.Coding.TannerLiftedProduct
