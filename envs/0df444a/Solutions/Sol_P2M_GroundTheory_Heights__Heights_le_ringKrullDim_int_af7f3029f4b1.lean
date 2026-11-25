-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_le_ringKrullDim_int_af7f3029f4b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:25:32.515538+00:00
-- url     : https://prove2.me/submissions/d36b2654-d6b5-43e2-bbca-7084f5701596

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IntDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IntDimBounds
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isJacobsonRing_int_223cc283b912
import Theorems.Thm_ReciprocityTheory_CA_height_eq_of_isMaximal_of_trdeg_eq_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Algebra Cardinal
open scoped TensorProduct
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (B : Type) [CommRing B] [IsDomain B] [Algebra.FiniteType ℤ B]
    (hinj : Function.Injective (algebraMap ℤ B)) (t : ℕ) (ht : trdeg ℤ B = t) :
    (((t + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim B := by
  letI : Algebra B (ℚ ⊗[ℤ] B) := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)
  have hM : M ≤ nonZeroDivisors B := by
    rintro _ ⟨n, hn, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    exact nonZeroDivisors.ne_zero hn (hinj (h.trans (map_zero _).symm))
  haveI : IsLocalization M (ℚ ⊗[ℤ] B) := IsLocalization.tensorRight _ _
  haveI : IsDomain (ℚ ⊗[ℤ] B) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM

  have hBL : Function.Injective (algebraMap B (ℚ ⊗[ℤ] B)) := IsLocalization.injective _ hM
  haveI : FaithfulSMul B (ℚ ⊗[ℤ] B) := (faithfulSMul_iff_algebraMap_injective _ _).2 hBL
  haveI : FaithfulSMul ℤ B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : FaithfulSMul ℤ ℚ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap ℤ ℚ).injective_int
  haveI : FaithfulSMul ℚ (ℚ ⊗[ℤ] B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap ℚ (ℚ ⊗[ℤ] B)).injective
  haveI := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (ℚ ⊗[ℤ] B))
    ((algebraMap B (ℚ ⊗[ℤ] B)).comp (algebraMap ℤ B)))
  haveI := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (ℚ ⊗[ℤ] B))
    ((algebraMap ℚ (ℚ ⊗[ℤ] B)).comp (algebraMap ℤ ℚ)))
  haveI : Algebra.IsAlgebraic B (ℚ ⊗[ℤ] B) := IsLocalization.isAlgebraic _ M
  haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have h1 := trdeg_add_eq ℤ B (A := ℚ ⊗[ℤ] B)
  have h2 := trdeg_add_eq ℤ ℚ (A := ℚ ⊗[ℤ] B)
  rw [trdeg_eq_zero (R := B) (A := ℚ ⊗[ℤ] B), add_zero] at h1
  rw [trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add] at h2
  have htL : trdeg ℚ (ℚ ⊗[ℤ] B) = t := by rw [h2, ← h1, ht]

  obtain ⟨m, hm⟩ := Ideal.exists_maximal (ℚ ⊗[ℤ] B)
  have hmh : m.height = t := ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field (K := ℚ) t htL m
  have hPh : (m.under B).height = t := (IsLocalization.height_under M m).trans hmh
  have hdisj : Disjoint (M : Set B) (m.under B) :=
    (IsLocalization.disjoint_under_iff M _ m).2 hm.ne_top
  have hnm : ¬ (m.under B).IsMaximal := by
    intro hPm
    letI := Ideal.Quotient.field (m.under B)
    haveI : IsJacobsonRing ℤ := isJacobsonRing_int
    haveI : Algebra.FiniteType ℤ (B ⧸ m.under B) :=
      .of_surjective (Ideal.Quotient.mkₐ ℤ _) (Ideal.Quotient.mkₐ_surjective ℤ _)
    haveI := finite_of_finite_type_of_isJacobsonRing ℤ (B ⧸ m.under B)
    haveI : Algebra.IsIntegral ℤ (B ⧸ m.under B) := Algebra.IsIntegral.of_finite ℤ _
    apply Int.not_isField
    refine isField_of_isIntegral_of_isField ?_ (Field.toIsField (B ⧸ m.under B))
    have e : algebraMap ℤ (B ⧸ m.under B) = (Ideal.Quotient.mk _).comp (algebraMap ℤ B) :=
      RingHom.ext_int _ _
    rw [e, injective_iff_map_eq_zero]
    intro n hn
    by_contra hn0
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hn
    exact Set.disjoint_left.mp hdisj ⟨n, mem_nonZeroDivisors_of_ne_zero hn0, rfl⟩ hn
  obtain ⟨N, hN, hPN⟩ := (m.under B).exists_le_maximal (Ideal.IsPrime.ne_top inferInstance)
  have hlt : m.under B < N := lt_of_le_of_ne hPN (fun h => hnm (h ▸ hN))
  have hh := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hPh] at hh
  calc (((t + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (N.height : WithBot ℕ∞) := by
        exact_mod_cast hh
    _ ≤ ringKrullDim B := Ideal.height_le_ringKrullDim_of_isPrime
end GroundTheory.Heights₂.Heights
