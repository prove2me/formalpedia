-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeIndex_orbit_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:15:04.008624+00:00
-- url     : https://prove2.me/submissions/629f5fc2-d0a1-4278-9e40-d7e1c9f7ff22

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Mathlib.GroupTheory.GroupAction.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperMatrix_doubleCoset
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    letI := lpsHeckeIndexAction N p hNp
    MulAction.orbit (CongruenceSubgroup.Gamma0 N) (none:Option (Fin p))=Set.univ := by
  let := lpsHeckeIndexAction N p hNp
  apply Set.eq_univ_of_forall
  intro i
  obtain ⟨δ,γ,_hδ,hγ,he⟩ := lpsHeckeUpperMatrix_doubleCoset N p hNp i
  have hf : lpsHeckeUpperMatrix p none*(γ:Matrix (Fin 2) (Fin 2) ℤ)=
      ((δ⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p i := by
    rw [he,←Matrix.mul_assoc,←Matrix.mul_assoc,←Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one,Matrix.one_mul]
  refine ⟨⟨γ⁻¹,(CongruenceSubgroup.Gamma0 N).inv_mem hγ⟩,?_⟩
  change lpsHeckeRightIndex N p hNp (γ⁻¹)⁻¹ _ none=i
  simpa only [inv_inv] using lpsHeckeRightIndex_of_factor N p hNp γ hγ none i δ⁻¹ hf
end QEC.Coding.TannerLiftedProduct
