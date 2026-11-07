-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspCosetComponent_slash_covariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:03.810408+00:00
-- url     : https://prove2.me/submissions/c922812f-9c6a-4ee2-bcde-4008125ac3c1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : SL(2,ℤ)) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (lpsCuspCosetComponent N f (h • γ)) ∣[(2:ℤ)] h=lpsCuspCosetComponent N f γ := by
  refine QuotientGroup.induction_on γ (fun j => ?_)
  change ((f:ℍ→ℂ) ∣[(2:ℤ)] (h*j)⁻¹) ∣[(2:ℤ)] h=(f:ℍ→ℂ) ∣[(2:ℤ)] j⁻¹
  rw [← SlashAction.slash_mul]
  simp [mul_inv_rev,mul_assoc]
end QEC.Coding.TannerLiftedProduct
