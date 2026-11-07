-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:24:18.300019+00:00
-- url     : https://prove2.me/submissions/28a0b7e5-31f7-47b2-8430-0e83e73cfc78

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
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
    (τ : ℍ) : 0≤lpsCuspPeterssonDensity N f τ := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  simp only [lpsCuspPeterssonDensity,lpsCuspPeterssonTrace,Complex.re_sum]
  exact Finset.sum_nonneg (fun γ _ => lpsCuspCosetPetersson_self_nonneg N f τ γ)
end QEC.Coding.TannerLiftedProduct
