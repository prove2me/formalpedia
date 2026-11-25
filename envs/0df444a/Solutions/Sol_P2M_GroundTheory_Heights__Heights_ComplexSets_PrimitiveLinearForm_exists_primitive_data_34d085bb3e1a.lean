-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_exists_primitive_data_34d085bb3e1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:00:02.34484+00:00
-- url     : https://prove2.me/submissions/6f554dcc-a346-44a1-b646-61efd7230a10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PrimitiveLinearForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_isLocalization_tensor_97cba6a547bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_exists_linear_primitive_67c803d2091d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open Polynomial TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveLinearForm
variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
attribute [local instance] tensorRightAlgebra
namespace GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveLinearForm
theorem _root_.solution {R B : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Module.Finite R B]
    (hinj : Function.Injective (algebraMap R B)) (ι : ℂ →+* R) {n : ℕ} (x : Fin n → B)
    (hx : Algebra.adjoin R (Set.range x) = ⊤) :
    ∃ (c : Fin n → ℂ) (m : R[X]) (D : R) (Q : Fin n → R[X]),
      m.Monic ∧ m.natDegree = Module.finrank (FractionRing R) (FractionRing R ⊗[R] B) ∧
      (∀ p : R[X], aeval (∑ j, algebraMap R B (ι (c j)) * x j) p = 0 ↔ m ∣ p) ∧
      D ≠ 0 ∧ (∃ a b : R[X], a * m + b * derivative m = C D) ∧
      ∀ j, algebraMap R B D * x j = aeval (∑ j, algebraMap R B (ι (c j)) * x j) (Q j) := by
  classical
  let K := FractionRing R
  let L := K ⊗[R] B
  let _ : Algebra B L := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) L :=
    isLocalization_tensor R B
  have hM : Algebra.algebraMapSubmonoid B (nonZeroDivisors R) ≤ nonZeroDivisors B := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero hr (hinj (by rw [h, map_zero])))
  have : IsDomain L := IsLocalization.isDomain_of_le_nonZeroDivisors L hM
  have hBL : Function.Injective (algebraMap B L) := IsLocalization.injective L hM
  have : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
  let _ : Field L := (isField_of_isIntegral_of_isField' (R := K) (Field.toIsField K)).toField
  let ιK : ℂ →+* K := (algebraMap R K).comp ι
  have : CharZero K := ⟨fun a b h => by
    have h' : ιK (a : ℂ) = ιK (b : ℂ) := by simpa [map_natCast] using h
    exact_mod_cast ιK.injective h'⟩
  have : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hxgen : ∀ φ ψ : L →ₐ[K] AlgebraicClosure K,
      (∀ j, φ (algebraMap B L (x j)) = ψ (algebraMap B L (x j))) → φ = ψ := by
    intro φ ψ h
    have h1 : (φ.restrictScalars R).comp (IsScalarTower.toAlgHom R B L) =
        (ψ.restrictScalars R).comp (IsScalarTower.toAlgHom R B L) := by
      apply AlgHom.ext_of_adjoin_eq_top hx
      rintro _ ⟨j, rfl⟩
      exact h j
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))
    exact RingHom.ext fun b => AlgHom.congr_fun h1 b
  obtain ⟨c, hc⟩ := exists_linear_primitive ιK (fun j => algebraMap B L (x j)) hxgen
  refine ⟨c, ?_⟩
  set ℓ : B := ∑ j, algebraMap R B (ι (c j)) * x j with hℓ
  have hℓL : algebraMap B L ℓ = ∑ j, algebraMap K L (ιK (c j)) * algebraMap B L (x j) := by
    rw [hℓ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply R K L]
    rfl
  rw [← hℓL] at hc
  have : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  have hint : IsIntegral R ℓ := Algebra.IsIntegral.isIntegral ℓ
  have hmK : minpoly K (algebraMap B L ℓ) = (minpoly R ℓ).map (algebraMap R K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  have hdeg : (minpoly R ℓ).natDegree = Module.finrank K L := by
    rw [← (minpoly.monic hint).natDegree_map (algebraMap R K), ← hmK]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq K _).mp hc
  have : Module.IsTorsionFree R B := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hdiv : ∀ p : R[X], aeval ℓ p = 0 ↔ minpoly R ℓ ∣ p := fun p =>
    ⟨minpoly.isIntegrallyClosed_dvd hint, fun ⟨q, hq⟩ => by rw [hq, map_mul, minpoly.aeval, zero_mul]⟩

  have hirr : Irreducible ((minpoly R ℓ).map (algebraMap R K)) :=
    hmK ▸ minpoly.irreducible (IsIntegral.of_finite K _)
  have hsep : IsCoprime ((minpoly R ℓ).map (algebraMap R K))
      (derivative ((minpoly R ℓ).map (algebraMap R K))) := hirr.separable
  obtain ⟨a, b, hab⟩ := hsep
  rw [Polynomial.derivative_map] at hab
  obtain ⟨α, hα, hαa⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) a
  obtain ⟨β, hβ, hβb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) b
  have hinjK : Function.Injective (Polynomial.map (algebraMap R K)) :=
    Polynomial.map_injective _ (IsFractionRing.injective R K)
  have hid : C β * IsLocalization.integerNormalization (nonZeroDivisors R) a * minpoly R ℓ +
      C α * IsLocalization.integerNormalization (nonZeroDivisors R) b * derivative (minpoly R ℓ) =
      C (α * β) := by
    apply hinjK
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hαa, hβb,
      Algebra.smul_def, Polynomial.algebraMap_apply, map_mul]
    linear_combination (C (algebraMap R K α) * C (algebraMap R K β)) * hab

  have hmem : ∀ j, ∃ P : K[X], aeval (algebraMap B L ℓ) P = algebraMap B L (x j) := by
    intro j
    have h1 : algebraMap B L (x j) ∈ (IntermediateField.adjoin K {algebraMap B L ℓ}).toSubalgebra := by
      rw [hc]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _), Algebra.adjoin_singleton_eq_range_aeval] at h1
    obtain ⟨P, hP⟩ := h1
    exact ⟨P, hP⟩
  choose P hP using hmem
  have hclear : ∀ j, ∃ e ∈ nonZeroDivisors R, ∃ P' : R[X], aeval ℓ P' = algebraMap R B e * x j := by
    intro j
    obtain ⟨e, he, hPe⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) (P j)
    refine ⟨e, he, IsLocalization.integerNormalization (nonZeroDivisors R) (P j), hBL ?_⟩
    rw [← Polynomial.aeval_algebraMap_apply, ← Polynomial.aeval_map_algebraMap K, hPe,
      Algebra.smul_def, Polynomial.algebraMap_apply, map_mul, Polynomial.aeval_C, hP j, map_mul,
      ← IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply R K L]
  choose e he Q' hQ' using hclear
  refine ⟨minpoly R ℓ, α * β * ∏ j, e j,
    fun j => C (α * β * ∏ k ∈ Finset.univ.erase j, e k) * Q' j, minpoly.monic hint, hdeg, hdiv,
    ?_, ?_, ?_⟩
  · refine mul_ne_zero (mul_ne_zero (nonZeroDivisors.ne_zero hα) (nonZeroDivisors.ne_zero hβ)) ?_
    exact Finset.prod_ne_zero_iff.mpr fun j _ => nonZeroDivisors.ne_zero (he j)
  · refine ⟨C (∏ j, e j) * (C β * IsLocalization.integerNormalization (nonZeroDivisors R) a),
      C (∏ j, e j) * (C α * IsLocalization.integerNormalization (nonZeroDivisors R) b), ?_⟩
    rw [C_mul (a := α * β)]
    linear_combination C (∏ j, e j) * hid
  · intro j
    rw [map_mul (aeval ℓ), Polynomial.aeval_C, hQ' j, ← Finset.mul_prod_erase Finset.univ e
      (Finset.mem_univ j)]
    simp only [map_mul]
    ring
end GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveLinearForm
