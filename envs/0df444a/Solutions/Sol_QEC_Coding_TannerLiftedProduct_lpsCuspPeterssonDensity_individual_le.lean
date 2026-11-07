-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_individual_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:07:33.515208+00:00
-- url     : https://prove2.me/submissions/e8e662c1-23eb-454d-9ad7-2fd77e7b9aaf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoPetersson_self
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_self_nonneg
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
    (τ : ℍ) : ‖f τ‖^2*τ.im^2≤lpsCuspPeterssonDensity N f τ := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  have h := Finset.univ.single_le_sum
    (fun γ _ => lpsCuspCosetPetersson_self_nonneg N f τ γ)
    (Finset.mem_univ (⟦(1:SL(2,ℤ))⟧ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N))
  have ht : (lpsCuspCosetPetersson N f f τ ⟦(1:SL(2,ℤ))⟧).re=‖f τ‖^2*τ.im^2 := by
    rw [lpsCuspCosetPetersson_apply]
    simp only [inv_one,one_smul,lpsWeightTwoPetersson_self,Complex.ofReal_re]
  rw [ht] at h
  simpa only [lpsCuspPeterssonDensity,lpsCuspPeterssonTrace,Complex.re_sum] using h
end QEC.Coding.TannerLiftedProduct
