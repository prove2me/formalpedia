-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:07:44.668527+00:00
-- url     : https://prove2.me/submissions/512da4c0-b1ab-4cf8-8795-161dd536e727

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_covariant

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : SL(2,ℤ)) (τ : ℍ) :
    lpsCuspPeterssonTrace N f g (h • τ)=lpsCuspPeterssonTrace N f g τ := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  exact (Fintype.sum_equiv (MulAction.toPerm h) _ _
    (fun γ => (lpsCuspCosetPetersson_covariant N f g τ h γ).symm)).symm
end QEC.Coding.TannerLiftedProduct
