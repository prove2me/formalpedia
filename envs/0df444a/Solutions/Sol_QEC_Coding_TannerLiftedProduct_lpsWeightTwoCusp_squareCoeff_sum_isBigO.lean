-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareCoeff_sum_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:17:54.014791+00:00
-- url     : https://prove2.me/submissions/8f1224db-e491-4b33-942a-673459f13629

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareCoeff_nonneg
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_coeff_square_sum_bound


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    (fun X : ℕ => ∑ n ∈ Finset.Icc 1 X, lpsWeightTwoCusp_squareCoeff N f n)
      =O[atTop] (fun X : ℕ => (X:ℝ)^(2:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := lpsWeightTwoCusp_coeff_square_sum_bound N f
  refine isBigO_iff.mpr ⟨4*C,?_⟩
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun n hn => lpsWeightTwoCusp_squareCoeff_nonneg N f n)),
    Real.rpow_two,Real.norm_of_nonneg (sq_nonneg _)]
  have hsub : Finset.Icc 1 X⊆Finset.range (X+1) := by
    intro n hn
    exact Finset.mem_range.mpr (by have h := Finset.mem_Icc.mp hn;omega)
  calc
    _ ≤ ∑ n ∈ Finset.range (X+1), lpsWeightTwoCusp_squareCoeff N f n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n hn hnot => lpsWeightTwoCusp_squareCoeff_nonneg N f n)
    _ ≤ C*((X+1:ℕ):ℝ)^2 := hb (X+1)
    _ ≤ (4*C)*(X:ℝ)^2 := by
      have hXR : 1≤(X:ℝ) := by exact_mod_cast hX
      push_cast
      have hsq : ((X:ℝ)+1)^2≤4*(X:ℝ)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq hC]
end QEC.Coding.TannerLiftedProduct
