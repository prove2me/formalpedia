-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.extC_isRadical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:18.098569+00:00
-- url     : https://prove2.me/submissions/ce927c7b-73dc-4b01-9ee7-19627c7e2553

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_isReduced_tensor_of_essFiniteType


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime] : (extC 𝔭).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  have hA : IsDomain (MvPolynomial σ ℚ ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  have hK : IsReduced (TensorProduct ℚ (FractionRing (MvPolynomial σ ℚ ⧸ 𝔭)) ℂ) :=
    BaseChangeC.isReduced_tensor_of_essFiniteType _ ℂ
  have hK' : IsReduced (TensorProduct ℚ ℂ (FractionRing (MvPolynomial σ ℚ ⧸ 𝔭))) :=
    isReduced_of_injective (Algebra.TensorProduct.comm ℚ ℂ _) (Algebra.TensorProduct.comm ℚ ℂ _).injective
  have hinj : Function.Injective (Algebra.TensorProduct.map (1 : ℂ →ₐ[ℚ] ℂ)
      (IsScalarTower.toAlgHom ℚ (MvPolynomial σ ℚ ⧸ 𝔭) (FractionRing (MvPolynomial σ ℚ ⧸ 𝔭)))) :=
    Module.Flat.lTensor_preserves_injective_linearMap _
      (IsFractionRing.injective (MvPolynomial σ ℚ ⧸ 𝔭) (FractionRing (MvPolynomial σ ℚ ⧸ 𝔭)))
  have hT : IsReduced (TensorProduct ℚ ℂ (MvPolynomial σ ℚ ⧸ 𝔭)) := isReduced_of_injective _ hinj
  exact isReduced_of_injective (BaseChangeC.quotExtEquiv 𝔭).symm (BaseChangeC.quotExtEquiv 𝔭).symm.injective
end ReciprocityTheory.AnForm.R
