-- Prove2me | solution 1 for UniqueFactorizationMonoid.dvd_multiplicity_of_pow_eq_algebraMap_of_forall_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0afa1a54-1b3d-576a-b05f-ad283a654300

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UniqueFactorizationMonoid_dvd_multiplicity_of_pow_eq_algebraMap_of_forall_isUnramifiedAt

set_option autoImplicit false

open IsLocalRing Polynomial

namespace UniqueFactorizationMonoid
namespace KVal
p2m_open "UniqueFactorizationMonoid"

theorem dvd_of_pow_eq_pow_mul_unit {L : Type*} [CommRing L] [IsDomain L] [IsDiscreteValuationRing L]
    {π : L} (hπ : Irreducible π) {y : L} (hy : y ≠ 0) {k n : ℕ} (r : Lˣ) (h : y ^ k = π ^ n * r) :
    k ∣ n := by
  obtain ⟨a, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ
  have : ((v ^ k : Lˣ) : L) * π ^ (a * k) = (r : L) * π ^ n := by
    rw [Units.val_pow_eq_pow_val, pow_mul, ← mul_pow, ← hv, h, mul_comm]
  have hke := IsDiscreteValuationRing.unit_mul_pow_congr_pow hπ hπ _ _ _ _ this
  exact ⟨a, by rw [mul_comm]; exact hke.symm⟩

end UniqueFactorizationMonoid.KVal

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [IsNoetherianRing R]
    (p : R) (hp : Prime p) (e : ℕ) (he : 0 < e) (f : R) (hf : f ≠ 0)
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsNoetherianRing B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (K₀ : Type*) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra R F] [IsScalarTower R K₀ F]
    [Algebra B F] [IsScalarTower R B F] [IsFractionRing B F]
    (α : F) (hα : α ^ e = algebraMap R F f)
    (hunr : ∀ (𝔓 : Ideal B) [𝔓.IsPrime], 𝔓.comap (algebraMap R B) = Ideal.span {p} → Algebra.IsUnramifiedAt R 𝔓) :
    e ∣ multiplicity p f := by
  classical
  have hinjRB : Function.Injective (algebraMap R B) := FaithfulSMul.algebraMap_injective R B
  have hinjBF : Function.Injective (algebraMap B F) := IsFractionRing.injective B F
  have hinjRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R B F]; exact hinjBF.comp hinjRB
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B

  set 𝔭 : Ideal R := Ideal.span {p} with h𝔭
  haveI h𝔭pr : 𝔭.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  obtain ⟨𝔓, -, h𝔓pr, h𝔓⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔭 (⊥ : Ideal B)
    (by rw [Ideal.comap_bot_of_injective _ hinjRB]; exact bot_le)
  haveI := h𝔓pr
  haveI hlo : 𝔓.LiesOver 𝔭 := ⟨by rw [Ideal.under_def, h𝔓]⟩
  have hU : Algebra.IsUnramifiedAt R 𝔓 := hunr 𝔓 h𝔓

  letI := Localization.AtPrime.algebraOfLiesOver 𝔭 𝔓
  have hmap : 𝔭.map (algebraMap R (Localization.AtPrime 𝔓)) = maximalIdeal (Localization.AtPrime 𝔓) :=
    ((Algebra.isUnramifiedAt_iff_map_eq R 𝔭 𝔓).mp hU).2
  have hmax : maximalIdeal (Localization.AtPrime 𝔓) = Ideal.span {algebraMap R (Localization.AtPrime 𝔓) p} := by
    rw [← hmap, h𝔭, Ideal.map_span, Set.image_singleton]
  have hinjRL : Function.Injective (algebraMap R (Localization.AtPrime 𝔓)) := by
    rw [IsScalarTower.algebraMap_eq R B (Localization.AtPrime 𝔓)]
    exact (IsLocalization.injective (Localization.AtPrime 𝔓) 𝔓.primeCompl_le_nonZeroDivisors).comp hinjRB
  set π : Localization.AtPrime 𝔓 := algebraMap R (Localization.AtPrime 𝔓) p with hπdef
  have hπ0 : π ≠ 0 := (map_ne_zero_iff _ hinjRL).mpr hp.ne_zero

  haveI : IsNoetherianRing (Localization.AtPrime 𝔓) :=
    IsLocalization.isNoetherianRing 𝔓.primeCompl _ inferInstance
  have hnf : ¬ IsField (Localization.AtPrime 𝔓) := by
    intro hF
    apply hπ0
    have : maximalIdeal (Localization.AtPrime 𝔓) = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hF
    rw [hmax, Ideal.span_singleton_eq_bot] at this
    exact this
  have hprinc : (maximalIdeal (Localization.AtPrime 𝔓)).IsPrincipal := ⟨⟨π, hmax⟩⟩
  haveI hDVR : IsDiscreteValuationRing (Localization.AtPrime 𝔓) :=
    ((IsDiscreteValuationRing.TFAE (Localization.AtPrime 𝔓) hnf).out 0 4).mpr hprinc
  have hπirr : Irreducible π := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π hπ0 hmax

  have hunits : ∀ y : 𝔓.primeCompl, IsUnit (algebraMap B F y) := by
    intro y
    apply isUnit_iff_ne_zero.mpr
    intro h0
    exact y.2 (by rw [show (y : B) = 0 from hinjBF (by rw [h0, map_zero])]; exact 𝔓.zero_mem)
  letI algLF : Algebra (Localization.AtPrime 𝔓) F := (IsLocalization.lift (M := 𝔓.primeCompl) (S := Localization.AtPrime 𝔓) hunits).toAlgebra
  have halg : ∀ b : B, algebraMap (Localization.AtPrime 𝔓) F (algebraMap B (Localization.AtPrime 𝔓) b) = algebraMap B F b :=
    fun b => IsLocalization.lift_eq hunits b
  haveI : IsScalarTower B (Localization.AtPrime 𝔓) F := IsScalarTower.of_algebraMap_eq (fun b => (halg b).symm)
  haveI hLfrac : IsFractionRing (Localization.AtPrime 𝔓) F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔓.primeCompl (Localization.AtPrime 𝔓) F
  have hinjLF : Function.Injective (algebraMap (Localization.AtPrime 𝔓) F) := IsFractionRing.injective _ _
  have hRLF : ∀ r : R, algebraMap (Localization.AtPrime 𝔓) F (algebraMap R (Localization.AtPrime 𝔓) r) = algebraMap R F r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R B (Localization.AtPrime 𝔓), halg, ← IsScalarTower.algebraMap_apply]

  set m := multiplicity p f with hm
  obtain ⟨g, hfg, hpg⟩ : ∃ g : R, f = p ^ m * g ∧ ¬ p ∣ g :=
    (FiniteMultiplicity.of_not_isUnit hp.not_unit hf).exists_eq_pow_mul_and_not_dvd
  have hgunit : IsUnit (algebraMap R (Localization.AtPrime 𝔓) g) := by
    rw [IsScalarTower.algebraMap_apply R B (Localization.AtPrime 𝔓)]
    apply IsLocalization.map_units (Localization.AtPrime 𝔓) (⟨algebraMap R B g, ?_⟩ : 𝔓.primeCompl)
    intro hg𝔓
    apply hpg
    have : g ∈ 𝔓.comap (algebraMap R B) := hg𝔓
    rw [h𝔓, h𝔭, Ideal.mem_span_singleton] at this
    exact this

  obtain ⟨x, y, hy, hαxy⟩ := IsFractionRing.div_surjective (A := Localization.AtPrime 𝔓) α
  have hy0 : (y : Localization.AtPrime 𝔓) ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    intro hx0
    have hα0 : α = 0 := by rw [← hαxy, hx0, map_zero, zero_div]
    have : algebraMap R F f = 0 := by rw [← hα, hα0, zero_pow he.ne']
    exact hf ((map_eq_zero_iff _ hinjRF).mp this)
  obtain ⟨b, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπirr
  have hyF0 : algebraMap (Localization.AtPrime 𝔓) F y ≠ 0 := (map_ne_zero_iff _ hinjLF).mpr hy0
  have h2 : x ^ e = algebraMap R (Localization.AtPrime 𝔓) f * y ^ e := by
    apply hinjLF
    rw [map_pow, map_mul, map_pow, hRLF, ← hα, ← hαxy, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hyF0)]
  have hxe : x ^ e = π ^ (m + b * e) * ((hgunit.unit * v ^ e : (Localization.AtPrime 𝔓)ˣ) : Localization.AtPrime 𝔓) := by
    rw [h2, hfg, map_mul, map_pow, ← hπdef, hv, Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, pow_add,
      pow_mul, mul_pow]
    ring
  have h3 : e ∣ m + b * e := UniqueFactorizationMonoid.KVal.dvd_of_pow_eq_pow_mul_unit hπirr hx0 _ hxe
  exact (Nat.dvd_add_left (dvd_mul_left e b)).mp h3

end S_UniqueFactorizationMonoid_dvd_multiplicity_of_pow_eq_algebraMap_of_forall_isUnramifiedAt
end P2MW
export P2MW.S_UniqueFactorizationMonoid_dvd_multiplicity_of_pow_eq_algebraMap_of_forall_isUnramifiedAt (solution)
