-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:06:05.03527+00:00
-- url     : https://prove2.me/submissions/8e694f2d-08ec-4dcb-b5f9-e6db560a8431

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
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    Continuous (fun τ => lpsCuspCosetPetersson N f g τ γ) := by
  refine QuotientGroup.induction_on γ (fun h => ?_)
  change Continuous (fun τ => petersson 2 f g (h⁻¹ • τ))
  apply (petersson_continuous 2 (by fun_prop) (by fun_prop)).comp
  change Continuous (fun τ : ℍ => h⁻¹ • τ)
  simpa only [ModularGroup.sl_moeb] using
    (show Continuous (fun τ : ℍ => ((h⁻¹ : SL(2,ℤ)) : GL (Fin 2) ℝ) • τ) from continuous_const_smul _)
end QEC.Coding.TannerLiftedProduct
