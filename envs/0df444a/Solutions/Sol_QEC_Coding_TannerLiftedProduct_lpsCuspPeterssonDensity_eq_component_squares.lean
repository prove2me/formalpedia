-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_eq_component_squares
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:05.163556+00:00
-- url     : https://prove2.me/submissions/693d4e8b-6096-4f5a-8f46-fe6562fae7cf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoPetersson_self
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetComponent_petersson
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) :
    lpsCuspPeterssonDensity N f τ=
      τ.im^2*lpsCuspComponentSquareSum N f τ := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  simp only [lpsCuspPeterssonDensity,lpsCuspPeterssonTrace,Complex.re_sum,lpsCuspComponentSquareSum]
  calc
    _ = ∑γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, τ.im^2*‖lpsCuspCosetComponent N f γ τ‖^2 := by
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [lpsCuspCosetComponent_petersson,lpsWeightTwoPetersson_self,Complex.ofReal_re,mul_comm]
    _ = _ := (Finset.mul_sum _ _ _).symm
end QEC.Coding.TannerLiftedProduct
