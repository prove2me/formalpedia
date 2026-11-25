-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.BaseChangeC.isReduced_tensor_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:16.797921+00:00
-- url     : https://prove2.me/submissions/b9f5a65e-6675-4b97-89a6-394083c38f4c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA

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
attribute [-instance] DivisionRing.toRatAlgebra
namespace ReciprocityTheory.AnForm.R.BaseChangeC
theorem _root_.solution (F K D : Type) [Field F] [Field K] [Algebra F K]
    [Algebra.FormallyUnramified F K] [Algebra.EssFiniteType F K] [CommRing D] [IsDomain D]
    [Algebra F D] : IsReduced (K ⊗[F] D) := by
  let M := FractionRing D
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id F K)
      (IsScalarTower.toAlgHom F D M)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  have : IsReduced (K ⊗[F] M) := by
    have := Algebra.FormallyUnramified.isReduced_of_field M (M ⊗[F] K)
    exact isReduced_of_injective (Algebra.TensorProduct.comm F K M).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm F K M).injective
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id F K)
      (IsScalarTower.toAlgHom F D M)).toRingHom hinj
end ReciprocityTheory.AnForm.R.BaseChangeC
