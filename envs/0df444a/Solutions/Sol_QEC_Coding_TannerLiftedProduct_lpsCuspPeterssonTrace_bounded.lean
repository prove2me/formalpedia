-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:06:07.009292+00:00
-- url     : https://prove2.me/submissions/028949c6-082d-4693-b989-0d8f76f677e3

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
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃C,∀τ,‖lpsCuspPeterssonTrace N f g τ‖≤C := by
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  obtain ⟨C,hC⟩ := CuspFormClass.petersson_bounded_left 2 _ f g
  refine ⟨(Fintype.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N):ℝ)*C,fun τ => ?_⟩
  calc
    ‖lpsCuspPeterssonTrace N f g τ‖ ≤ ∑γ,‖lpsCuspCosetPetersson N f g τ γ‖ := norm_sum_le _ _
    _ ≤ ∑_γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, C := by
      apply Finset.sum_le_sum
      intro γ hγ
      induction γ using QuotientGroup.induction_on
      exact hC _
    _ = _ := by simp
end QEC.Coding.TannerLiftedProduct
