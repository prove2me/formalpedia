-- Prove2me | solution 1 for ValuationSubring.exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/bc619f9e-5f47-5be9-b0be-b05bae53db85

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_pow_of_isDiscreteValuationRing
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_conj_mul_pow_inv_mem_inertiaSubgroupIn_and_wild
import Theorems.Thm_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_of_wild_of_normal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild_of_isDiscreteValuationRing

set_option autoImplicit false

namespace P2mKcMonoGalDvr

theorem liesOverPrime_of_ne_top
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (p : ℕ) (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) (hAtop : A ≠ ⊤) :
    A.LiesOverPrime p := by
  classical
  unfold ValuationSubring.LiesOverPrime
  by_contra hpu
  apply hAtop

  have hpA : (p : Ω) ∈ A := natCast_mem A p
  have hvp : A.valuation (p : Ω) = 1 :=
    le_antisymm (A.valuation_le_one_iff _ |>.mpr hpA) (not_lt.mp fun h => hpu (A.mem_nonunits_iff.mpr h))
  have hp0 : (p : Ω) ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hvp]; exact one_ne_zero)
  have hpΩ : (p : Ω) = algebraMap K Ω (algebraMap R K (p : R)) := by simp
  have hpR0 : (p : R) ≠ 0 := by
    intro h
    apply hp0
    rw [hpΩ, h, map_zero, map_zero]

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨e, u, hpe⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hpR0 hπ
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hpe
    exact (IsLocalRing.mem_maximalIdeal _).mp hp (hpe ▸ u.isUnit)
  set ι : R →+* Ω := (algebraMap K Ω).comp (algebraMap R K) with hιdef
  have hι : ∀ r : R, ι r ∈ A := fun r => hA r
  have hιinj : Function.Injective ι :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  have hπ0 : ι π ≠ 0 := (map_ne_zero_iff ι hιinj).mpr hπ.ne_zero

  have hpinvA : (p : Ω)⁻¹ ∈ A := (A.valuation_le_one_iff _).mp (by rw [map_inv₀, hvp, inv_one])
  have hπeinv : (ι π ^ e)⁻¹ ∈ A := by
    have h1 : ι π ^ e = ι (↑u⁻¹ : R) * (p : Ω) := by
      rw [← map_pow, hpΩ]
      change ι (π ^ e) = ι (↑u⁻¹ : R) * ι (p : R)
      rw [← map_mul, hpe, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h1, mul_inv]
    refine mul_mem ?_ hpinvA
    have h2 : (ι (↑u⁻¹ : R))⁻¹ = ι (u : R) := by
      have : ι (↑u⁻¹ : R) * ι (u : R) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      exact (eq_inv_of_mul_eq_one_right this).symm
    rw [h2]
    exact hι u
  have hπinv : (ι π)⁻¹ ∈ A := by
    rw [← A.valuation_le_one_iff] at hπeinv ⊢
    rw [← inv_pow, map_pow] at hπeinv
    exact (pow_le_one_iff he).mp hπeinv

  have hKA : ∀ y : K, algebraMap K Ω y ∈ A := by
    intro y
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) y
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨n, v, hbv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
    rw [map_div₀]
    change ι a / ι b ∈ A
    rw [div_eq_mul_inv]
    refine mul_mem (hι a) ?_
    rw [hbv, map_mul, map_pow, mul_inv, ← inv_pow]
    refine mul_mem ?_ (pow_mem hπinv n)
    have h2 : (ι (v : R))⁻¹ = ι (↑v⁻¹ : R) := by
      have : ι (v : R) * ι (↑v⁻¹ : R) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      exact (eq_inv_of_mul_eq_one_right this).symm
    rw [h2]
    exact hι _

  refine top_unique fun z _ => ?_
  let φ : K →+* ↥A :=
    { toFun := fun y => ⟨algebraMap K Ω y, hKA y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  have hzK : IsIntegral K z := (Algebra.IsAlgebraic.isAlgebraic (R := K) z).isIntegral
  have hzA : IsIntegral ↥A z := by
    obtain ⟨f, hf, hfz⟩ := hzK
    refine ⟨f.map φ, hf.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap ↥A Ω).comp φ = algebraMap K Ω := RingHom.ext fun _ => rfl
    rw [this]
    exact hfz
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := Ω)).mp hzA
  rw [← hy]
  exact y.2

end P2mKcMonoGalDvr

open P2mKcMonoGalDvr in
theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (p : ℕ) [Fact p.Prime] (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (A : ValuationSubring Ω) (hA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) (hAtop : A ≠ ⊤)
    (F : IntermediateField K Ω) [FiniteDimensional K ↥F] :
    ∃ (d : ℕ) (φ : Ω ≃ₐ[K] Ω), 0 < d ∧ (∀ z ∈ F, φ z = z) ∧ A.IsFrobeniusAt φ (p ^ d) ∧
      ∀ τ : Ω ≃ₐ[K] Ω, τ ∈ A.inertiaSubgroupIn K →
        φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹ ∈ A.inertiaSubgroupIn K ∧
        (∀ z : Ω, z ≠ 0 → (φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹) z * z⁻¹ - 1 ∈ A.nonunits) ∧
        ∀ (F' : IntermediateField K Ω) [FiniteDimensional K ↥F'] [Normal K ↥F'],
          ∃ a : ℕ, ∀ x ∈ F', ((φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹) ^ (p ^ a)) x = x := by
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨d, φ, hd, hfix, hφ⟩ :=
    ValuationSubring.exists_isFrobeniusAt_pow_of_isDiscreteValuationRing p hp A hA hAtop F
  refine ⟨d, φ, hd, hfix, hφ, fun τ hτ => ?_⟩
  obtain ⟨hmem, hwild⟩ := hφ.conj_mul_pow_inv_mem_inertiaSubgroupIn_and_wild hτ
  refine ⟨hmem, hwild, fun F' _ _ => ?_⟩
  exact ValuationSubring.exists_forall_pow_prime_pow_apply_eq_of_wild_of_normal (Fact.out : p.Prime) A
    (liesOverPrime_of_ne_top p hp A hA hAtop) hwild F'

end S_ValuationSubring_exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild_of_isDiscreteValuationRing
end P2MW
export P2MW.S_ValuationSubring_exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild_of_isDiscreteValuationRing (solution)
