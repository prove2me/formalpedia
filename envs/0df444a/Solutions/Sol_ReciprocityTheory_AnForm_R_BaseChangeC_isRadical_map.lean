-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.BaseChangeC.isRadical_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:14.929035+00:00
-- url     : https://prove2.me/submissions/89d14000-eb9e-4fc2-8edd-7b1c87a70bac

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_isReduced_tensor_of_essFiniteType


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.BaseChangeC
open MvPolynomial TensorProduct
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R.BaseChangeC
theorem _root_.solution (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime] : (Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  set A := MvPolynomial σ ℚ ⧸ 𝔭
  set K := FractionRing A
  have : Algebra.EssFiniteType ℚ K := inferInstanceAs (Algebra.EssFiniteType ℚ (Localization _))
  have h1 : IsReduced (K ⊗[ℚ] ℂ) := isReduced_tensor_of_essFiniteType K ℂ
  have h2 : IsReduced (ℂ ⊗[ℚ] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm ℚ ℂ K).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm ℚ ℂ K).injective
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ A K)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  have h3 : IsReduced (ℂ ⊗[ℚ] A) := isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ A K)).toRingHom hinj
  exact isReduced_of_injective (quotExtEquiv 𝔭).symm.toRingHom (quotExtEquiv 𝔭).symm.injective
end ReciprocityTheory.AnForm.R.BaseChangeC
