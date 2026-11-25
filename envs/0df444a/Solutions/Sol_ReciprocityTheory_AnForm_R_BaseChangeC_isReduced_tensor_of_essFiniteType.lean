-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.BaseChangeC.isReduced_tensor_of_essFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:52.408717+00:00
-- url     : https://prove2.me/submissions/15c48e97-4bd1-41c8-8806-67b9fc62a49b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_isDomain_tensor_of_isFractionRing
import Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_isReduced_tensor_domain

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
theorem _root_.solution (K : Type) [Field K] [Algebra ℚ K]
    [Algebra.EssFiniteType ℚ K] (C : Type) [Field C] [Algebra ℚ C] : IsReduced (K ⊗[ℚ] C) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ K
  set F0 := IntermediateField.adjoin ℚ (Set.range ((↑) : s → K))
  have : Algebra.IsAlgebraic F0 K := hs.isAlgebraic_field
  have : PerfectField F0 :=
    @PerfectField.ofCharZero F0 _ (charZero_of_injective_algebraMap (algebraMap ℚ F0).injective)
  have : Algebra.IsSeparable F0 K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.FormallyUnramified F0 K := Algebra.FormallyUnramified.of_isSeparable F0 K
  have : Algebra.EssFiniteType F0 K := Algebra.EssFiniteType.of_comp ℚ F0 K
  let e := hs.1.aevalEquivField
  letI : Algebra (MvPolynomial s ℚ) F0 :=
    (e.toRingEquiv.toRingHom.comp (algebraMap (MvPolynomial s ℚ) (FractionRing (MvPolynomial s ℚ)))).toAlgebra
  have := IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := MvPolynomial s ℚ) (A := F0)
    (Subsingleton.elim _ _)
  let e' : FractionRing (MvPolynomial s ℚ) ≃ₐ[MvPolynomial s ℚ] F0 :=
    { e.toRingEquiv with commutes' := fun _ => rfl }
  have : IsFractionRing (MvPolynomial s ℚ) F0 :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (MvPolynomial s ℚ)) e'
  have : IsDomain (F0 ⊗[ℚ] C) := isDomain_tensor_of_isFractionRing s F0 C
  have : IsReduced (K ⊗[F0] (F0 ⊗[ℚ] C)) := isReduced_tensor_domain F0 K (F0 ⊗[ℚ] C)
  exact isReduced_of_injective
    (Algebra.TensorProduct.cancelBaseChange ℚ F0 K K C).symm.toRingEquiv.toRingHom
    (Algebra.TensorProduct.cancelBaseChange ℚ F0 K K C).symm.injective
end ReciprocityTheory.AnForm.R.BaseChangeC
