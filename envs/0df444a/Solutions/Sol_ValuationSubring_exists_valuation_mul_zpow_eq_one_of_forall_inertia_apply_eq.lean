-- Prove2me | solution 1 for ValuationSubring.exists_valuation_mul_zpow_eq_one_of_forall_inertia_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/aaf0a949-5487-5aed-b9bd-baa24f572527

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_NumberField_ramificationIdx_under_fixedField_inertia_eq_one
import Theorems.Thm_ValuationSubring_valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_valuation_mul_zpow_eq_one_of_forall_inertia_apply_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open NumberField

namespace UVL

section dedekind
variable {A : Type*} [CommRing A] [IsDedekindDomain A]

theorem le_pow_iff_le_count [DecidableEq (Ideal A)] {x p : Ideal A} (hx : x ≠ ⊥) (hp : p.IsPrime) (hp0 : p ≠ ⊥) (n : ℕ) :
    x ≤ p ^ n ↔ n ≤ (UniqueFactorizationMonoid.normalizedFactors x).count p := by
  rw [← Ideal.dvd_iff_le, pow_dvd_iff_le_emultiplicity,
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors (Ideal.prime_of_isPrime hp0 hp).irreducible hx,
    normalize_eq]
  exact_mod_cast Iff.rfl

theorem exists_mem_pow_not_mem_pow_succ {p : Ideal A} (hp : p.IsPrime) (hp0 : p ≠ ⊥) {x : A} (hx : x ≠ 0) :
    ∃ n : ℕ, x ∈ p ^ n ∧ x ∉ p ^ (n + 1) := by
  classical
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors (Ideal.span {x})).count p, ?_, ?_⟩
  · rw [← Ideal.span_singleton_le_iff_mem, le_pow_iff_le_count (by simpa using hx) hp hp0]
  · rw [← Ideal.span_singleton_le_iff_mem, le_pow_iff_le_count (by simpa using hx) hp hp0]; omega

theorem exists_mem_not_mem_sq {p : Ideal A} (hp : p.IsPrime) (hp0 : p ≠ ⊥) : ∃ π ∈ p, π ∉ p ^ 2 := by
  have h := Ideal.pow_succ_lt_pow hp0 1
  rw [pow_one] at h
  obtain ⟨π, hπ, hπ2⟩ := SetLike.exists_of_lt h
  exact ⟨π, hπ, hπ2⟩

end dedekind

section transport
variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]

theorem algebraMap_mem_pow_ramificationIdx_mul (Q : Ideal B) (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥)
    (hmap0 : (Q.under A).map (algebraMap A B) ≠ ⊥)
    (a : A) (m : ℕ) (ha : a ∈ Q.under A ^ m) (ha' : a ∉ Q.under A ^ (m + 1)) :
    algebraMap A B a ∈ Q ^ ((Q.under A).ramificationIdx' Q * m) ∧
      algebraMap A B a ∉ Q ^ ((Q.under A).ramificationIdx' Q * m + 1) := by
  classical
  set 𝔮 := Q.under A with h𝔮
  set e := 𝔮.ramificationIdx' Q with he
  have h𝔮p : 𝔮.IsPrime := hQ.under A

  obtain ⟨I, hI⟩ : 𝔮 ^ m ∣ Ideal.span {a} := (Ideal.dvd_iff_le).mpr ((Ideal.span_singleton_le_iff_mem _).mpr ha)
  have hI𝔮 : ¬ I ≤ 𝔮 := by
    intro hle
    apply ha'
    rw [← Ideal.span_singleton_le_iff_mem, hI, pow_succ]
    exact Ideal.mul_mono_right hle
  have hmapI : ¬ I.map (algebraMap A B) ≤ Q := by
    rwa [Ideal.map_le_iff_le_comap]

  have hle : 𝔮.map (algebraMap A B) ≤ Q ^ e := Ideal.le_pow_ramificationIdx
  have hcount : (UniqueFactorizationMonoid.normalizedFactors (𝔮.map (algebraMap A B))).count Q = e :=
    (Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 hQ hQ0).symm
  have hpowle : (𝔮.map (algebraMap A B)) ^ m ≤ Q ^ (e * m) := by
    rw [pow_mul]; exact Ideal.pow_right_mono hle m
  have hpownle : ¬ (𝔮.map (algebraMap A B)) ^ m ≤ Q ^ (e * m + 1) := by
    rw [le_pow_iff_le_count (pow_ne_zero m hmap0) hQ hQ0, UniqueFactorizationMonoid.normalizedFactors_pow,
      Multiset.count_nsmul, hcount, mul_comm m e]
    omega
  have hspan : Ideal.span {algebraMap A B a} = (𝔮.map (algebraMap A B)) ^ m * I.map (algebraMap A B) := by
    rw [← Ideal.map_pow, ← Ideal.map_mul, ← hI, Ideal.map_span, Set.image_singleton]
  constructor
  · rw [← Ideal.span_singleton_le_iff_mem, hspan]
    exact Ideal.mul_le_left.trans hpowle
  · rw [← Ideal.span_singleton_le_iff_mem, hspan, ← Ideal.dvd_iff_le]
    intro hdvd
    have hQprime : Prime Q := Ideal.prime_of_isPrime hQ0 hQ
    have hndvd : ¬ Q ∣ I.map (algebraMap A B) := by rwa [Ideal.dvd_iff_le]
    have := hQprime.pow_dvd_of_dvd_mul_right (e * m + 1) hndvd hdvd
    exact hpownle (Ideal.dvd_iff_le.mp this)

end transport

theorem exists_valuation_eq_zpow (P : ValuationSubring (AlgebraicClosure ℚ))
    (M : Type) [Field M] [NumberField M] [Algebra M (AlgebraicClosure ℚ)]
    (Q : Ideal (𝓞 M)) [hQm : Q.IsMaximal] (hQ0 : Q ≠ ⊥)
    (hQle : ∀ x : 𝓞 M, P.valuation (algebraMap M (AlgebraicClosure ℚ) x) ≤ 1)
    (hQlt : ∀ x : 𝓞 M, x ∈ Q ↔ P.valuation (algebraMap M (AlgebraicClosure ℚ) x) < 1)
    (π : 𝓞 M) (hπ : π ∈ Q) (hπ2 : π ∉ Q ^ 2) (z : M) (hz : z ≠ 0) :
    ∃ k : ℤ, P.valuation (algebraMap M (AlgebraicClosure ℚ) z) = P.valuation (algebraMap M (AlgebraicClosure ℚ) π) ^ k := by

  obtain ⟨⟨a, b'⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 M)) (S := M) z
  set b : 𝓞 M := (b' : 𝓞 M) with hbdef
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero b'.2
  have hbM0 : algebraMap (𝓞 M) M b ≠ 0 := fun h => hb0 ((IsFractionRing.injective (𝓞 M) M) (by rw [h, map_zero]))
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hz
    have : z * algebraMap (𝓞 M) M b = 0 := by simpa using hab
    exact (mul_eq_zero.mp this).resolve_right hbM0
  obtain ⟨na, hna, hna'⟩ := exists_mem_pow_not_mem_pow_succ hQm.isPrime hQ0 ha0
  obtain ⟨nb, hnb, hnb'⟩ := exists_mem_pow_not_mem_pow_succ hQm.isPrime hQ0 hb0
  have hva := ValuationSubring.valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ P M Q hQle hQlt π hπ hπ2 na a hna hna'
  have hvb := ValuationSubring.valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ P M Q hQle hQlt π hπ hπ2 nb b hnb hnb'
  have hπv0 : P.valuation (algebraMap M (AlgebraicClosure ℚ) π) ≠ 0 := by
    rw [Valuation.ne_zero_iff, map_ne_zero_iff _ (algebraMap M (AlgebraicClosure ℚ)).injective]
    intro h
    apply hπ2
    have : π = 0 := by exact_mod_cast h
    simp [this]
  refine ⟨(na : ℤ) - (nb : ℤ), ?_⟩
  have hz' : algebraMap M (AlgebraicClosure ℚ) z =
      algebraMap M (AlgebraicClosure ℚ) a / algebraMap M (AlgebraicClosure ℚ) b := by
    rw [eq_div_iff ((map_ne_zero_iff _ (algebraMap M (AlgebraicClosure ℚ)).injective).mpr hbM0), ← map_mul]
    congr 1
  rw [hz', map_div₀, hva, hvb, zpow_sub₀ hπv0, zpow_natCast, zpow_natCast]

section mainproof

set_option maxHeartbeats 6400000 in
theorem main
    (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (ϖ : F) (hϖP : algebraMap F (AlgebraicClosure ℚ) ϖ ∈ P)
    (hirr : Irreducible (⟨ϖ, hϖP⟩ : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ)))))
    (M : IntermediateField F (AlgebraicClosure ℚ)) [FiniteDimensional F ↥M] [IsGalois F ↥M]
    (Q : Ideal (NumberField.RingOfIntegers ↥M)) [hQm : Q.IsMaximal]
    (hQle : ∀ x : NumberField.RingOfIntegers ↥M, P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) x) ≤ 1)
    (hQlt : ∀ x : NumberField.RingOfIntegers ↥M, x ∈ Q ↔ P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) x) < 1)
    (y : ↥M) (hy : y ≠ 0)
    (hfix : ∀ τ : ↥M ≃ₐ[F] ↥M, τ ∈ Q.inertia (↥M ≃ₐ[F] ↥M) → τ y = y) :
    ∃ n : ℤ, P.valuation (((y : AlgebraicClosure ℚ)) * (algebraMap F (AlgebraicClosure ℚ) ϖ) ^ n) = 1 := by
  classical

  haveI : IsScalarTower ℚ F ↥M := IsScalarTower.of_algebraMap_eq fun r => by rw [eq_ratCast, eq_ratCast, map_ratCast]
  haveI : CharZero ↥M := charZero_of_injective_algebraMap (algebraMap F ↥M).injective
  haveI : FiniteDimensional ℚ ↥M := Module.Finite.trans F ↥M
  haveI hNF : NumberField ↥M := @NumberField.mk _ _ inferInstance inferInstance

  set E : IntermediateField F ↥M := IntermediateField.fixedField (Q.inertia (↥M ≃ₐ[F] ↥M)) with hE
  have hyE : y ∈ E := (IntermediateField.mem_fixedField_iff _ _).mpr hfix
  haveI : IsScalarTower ℚ F ↥E := IsScalarTower.of_algebraMap_eq fun r => by rw [eq_ratCast, eq_ratCast, map_ratCast]
  haveI : CharZero ↥E := charZero_of_injective_algebraMap (algebraMap F ↥E).injective
  haveI : FiniteDimensional F ↥E := IntermediateField.finiteDimensional_left E
  haveI : FiniteDimensional ℚ ↥E := Module.Finite.trans F ↥E
  haveI hNE : NumberField ↥E := @NumberField.mk _ _ inferInstance inferInstance

  obtain ⟨-, hee⟩ := NumberField.ramificationIdx_under_fixedField_inertia_eq_one F ↥M Q E hE
  set e := (Q.under (𝓞 F)).ramificationIdx' Q with hedef

  have hqv : P.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff P).mp hP
  have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQm (NumberField.RingOfIntegers.not_isField ↥M)
  have hqQ : ((q : ℕ) : 𝓞 ↥M) ∈ Q := by
    rw [hQlt]; simpa using hqv
  have hq0M : ((q : ℕ) : 𝓞 ↥M) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hmapF0 : (Q.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 ↥M)) ≠ ⊥ := by
    intro h
    have : algebraMap (𝓞 F) (𝓞 ↥M) (q : ℕ) ∈ (Q.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 ↥M)) :=
      Ideal.mem_map_of_mem _ (by rw [Ideal.under_def, Ideal.mem_comap, map_natCast]; exact hqQ)
    rw [h, Ideal.mem_bot, map_natCast] at this
    exact hq0M this
  have hmapE0 : (Q.under (𝓞 ↥E)).map (algebraMap (𝓞 ↥E) (𝓞 ↥M)) ≠ ⊥ := by
    intro h
    have : algebraMap (𝓞 ↥E) (𝓞 ↥M) (q : ℕ) ∈ (Q.under (𝓞 ↥E)).map (algebraMap (𝓞 ↥E) (𝓞 ↥M)) :=
      Ideal.mem_map_of_mem _ (by rw [Ideal.under_def, Ideal.mem_comap, map_natCast]; exact hqQ)
    rw [h, Ideal.mem_bot, map_natCast] at this
    exact hq0M this
  have h𝔭0 : Q.under (𝓞 F) ≠ ⊥ := fun h => hmapF0 (by rw [h, Ideal.map_bot])
  have hQE0 : Q.under (𝓞 ↥E) ≠ ⊥ := fun h => hmapE0 (by rw [h, Ideal.map_bot])

  obtain ⟨πM, hπM, hπM2⟩ := exists_mem_not_mem_sq hQm.isPrime hQ0
  set V := P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) πM) with hVdef
  have hV0 : V ≠ 0 := by
    rw [hVdef, Valuation.ne_zero_iff, map_ne_zero_iff _ (algebraMap ↥M (AlgebraicClosure ℚ)).injective]
    intro h
    apply hπM2
    have : πM = 0 := by exact_mod_cast h
    simp [this]
  have hVlt : V < 1 := by rw [hVdef, ← hQlt]; exact hπM
  have hQle' : (Q.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 ↥M)) ≤ Q := Ideal.map_comap_le
  have he0 : e ≠ 0 := by
    rw [hedef]
    exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero hmapF0 hQm.isPrime hQle'
  set W := V ^ e with hWdef
  have hW0 : W ≠ 0 := pow_ne_zero e hV0
  have hWlt : W < 1 := pow_lt_one₀ zero_le' hVlt he0
  have hWpos : 0 < W := lt_of_le_of_ne zero_le' hW0.symm

  have hreadF : ∀ (c : 𝓞 F) (m : ℕ), c ∈ Q.under (𝓞 F) ^ m → c ∉ Q.under (𝓞 F) ^ (m + 1) →
      P.valuation (algebraMap F (AlgebraicClosure ℚ) c) = W ^ m := by
    intro c m hm hm'
    obtain ⟨h1, h2⟩ := algebraMap_mem_pow_ramificationIdx_mul Q hQm.isPrime hQ0 hmapF0 c m hm hm'
    have := ValuationSubring.valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ P ↥M Q hQle hQlt πM hπM hπM2
      _ _ h1 h2
    rw [← hedef] at this
    rw [hWdef, ← pow_mul, ← this]
    congr 1
  have hreadE : ∀ (c : 𝓞 ↥E) (m : ℕ), c ∈ Q.under (𝓞 ↥E) ^ m → c ∉ Q.under (𝓞 ↥E) ^ (m + 1) →
      P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) ((c : ↥E) : ↥M)) = W ^ m := by
    intro c m hm hm'
    obtain ⟨h1, h2⟩ := algebraMap_mem_pow_ramificationIdx_mul Q hQm.isPrime hQ0 hmapE0 c m hm hm'
    rw [hee] at h1 h2
    have := ValuationSubring.valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ P ↥M Q hQle hQlt πM hπM hπM2
      _ _ h1 h2
    rw [hWdef, ← pow_mul, ← this]
    congr 1

  have hfracF : ∀ z : F, z ≠ 0 → ∃ k : ℤ, P.valuation (algebraMap F (AlgebraicClosure ℚ) z) = W ^ k := by
    intro z hz
    obtain ⟨⟨a, b'⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) (S := F) z
    set b : 𝓞 F := (b' : 𝓞 F) with hbdef
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero b'.2
    have hbF0 : algebraMap (𝓞 F) F b ≠ 0 := fun h => hb0 ((IsFractionRing.injective (𝓞 F) F) (by rw [h, map_zero]))
    have ha0 : a ≠ 0 := by
      rintro rfl; apply hz
      have : z * algebraMap (𝓞 F) F b = 0 := by simpa using hab
      exact (mul_eq_zero.mp this).resolve_right hbF0
    obtain ⟨na, hna, hna'⟩ := exists_mem_pow_not_mem_pow_succ ((hQm.isPrime).under (𝓞 F)) h𝔭0 ha0
    obtain ⟨nb, hnb, hnb'⟩ := exists_mem_pow_not_mem_pow_succ ((hQm.isPrime).under (𝓞 F)) h𝔭0 hb0
    have hva := hreadF a na hna hna'
    have hvb := hreadF b nb hnb hnb'
    refine ⟨(na : ℤ) - (nb : ℤ), ?_⟩
    have hz' : algebraMap F (AlgebraicClosure ℚ) z =
        algebraMap F (AlgebraicClosure ℚ) a / algebraMap F (AlgebraicClosure ℚ) b := by
      rw [eq_div_iff ((map_ne_zero_iff _ (algebraMap F (AlgebraicClosure ℚ)).injective).mpr hbF0), ← map_mul]
      congr 1
    rw [hz', map_div₀, hva, hvb, zpow_sub₀ hW0, zpow_natCast, zpow_natCast]
  have hfracE : ∀ z : ↥E, z ≠ 0 → ∃ k : ℤ, P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) (z : ↥M)) = W ^ k := by
    intro z hz
    obtain ⟨⟨a, b'⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 ↥E)) (S := ↥E) z
    set b : 𝓞 ↥E := (b' : 𝓞 ↥E) with hbdef
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero b'.2
    have hbE0 : algebraMap (𝓞 ↥E) ↥E b ≠ 0 := fun h => hb0 ((IsFractionRing.injective (𝓞 ↥E) ↥E) (by rw [h, map_zero]))
    have ha0 : a ≠ 0 := by
      rintro rfl; apply hz
      have : z * algebraMap (𝓞 ↥E) ↥E b = 0 := by simpa using hab
      exact (mul_eq_zero.mp this).resolve_right hbE0
    obtain ⟨na, hna, hna'⟩ := exists_mem_pow_not_mem_pow_succ ((hQm.isPrime).under (𝓞 ↥E)) hQE0 ha0
    obtain ⟨nb, hnb, hnb'⟩ := exists_mem_pow_not_mem_pow_succ ((hQm.isPrime).under (𝓞 ↥E)) hQE0 hb0
    have hva := hreadE a na hna hna'
    have hvb := hreadE b nb hnb hnb'
    refine ⟨(na : ℤ) - (nb : ℤ), ?_⟩
    have hbM0 : algebraMap ↥M (AlgebraicClosure ℚ) ((b : ↥E) : ↥M) ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap ↥M (AlgebraicClosure ℚ)).injective]
      intro h
      apply hbE0
      have : (b : ↥E) = 0 := by exact_mod_cast h
      simpa using this
    have hz' : algebraMap ↥M (AlgebraicClosure ℚ) (z : ↥M) =
        algebraMap ↥M (AlgebraicClosure ℚ) ((a : ↥E) : ↥M) / algebraMap ↥M (AlgebraicClosure ℚ) ((b : ↥E) : ↥M) := by
      rw [eq_div_iff hbM0, ← map_mul]
      congr 1
      have := congrArg (fun w : ↥E => (w : ↥M)) hab
      simpa using this
    rw [hz', map_div₀, hva, hvb, zpow_sub₀ hW0, zpow_natCast, zpow_natCast]

  have hunit : ∀ x : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ))), IsUnit x → P.valuation (algebraMap F (AlgebraicClosure ℚ) (x : F)) = 1 := by
    intro x hx
    obtain ⟨w, hw⟩ := hx.exists_right_inv
    have h1 : P.valuation (algebraMap F (AlgebraicClosure ℚ) ((x * w : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ)))) : F)) = 1 := by
      rw [hw, show ((1 : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ)))) : F) = 1 from rfl, map_one, map_one]
    have hxle : P.valuation (algebraMap F (AlgebraicClosure ℚ) (x : F)) ≤ 1 := (P.valuation_le_one_iff _).mpr x.2
    have hwle : P.valuation (algebraMap F (AlgebraicClosure ℚ) (w : F)) ≤ 1 := (P.valuation_le_one_iff _).mpr w.2
    rw [show ((x * w : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ)))) : F) = (x : F) * (w : F) from rfl, map_mul, map_mul] at h1
    refine le_antisymm hxle (not_lt.mp fun hlt => ?_)
    have : P.valuation (algebraMap F (AlgebraicClosure ℚ) (x : F)) *
        P.valuation (algebraMap F (AlgebraicClosure ℚ) (w : F)) < 1 :=
      calc _ ≤ P.valuation (algebraMap F (AlgebraicClosure ℚ) (x : F)) * 1 := by gcongr
        _ < 1 := by rwa [mul_one]
    exact absurd h1 this.ne

  have hϖ0 : ϖ ≠ 0 := fun h => hirr.ne_zero (Subtype.ext h)
  have hvϖlt : P.valuation (algebraMap F (AlgebraicClosure ℚ) ϖ) < 1 := by
    have hle : P.valuation (algebraMap F (AlgebraicClosure ℚ) ϖ) ≤ 1 := (P.valuation_le_one_iff _).mpr hϖP
    refine lt_of_le_of_ne hle fun heq => hirr.not_isUnit ?_
    have hinvP : algebraMap F (AlgebraicClosure ℚ) ϖ⁻¹ ∈ P := by
      rw [← P.valuation_le_one_iff, map_inv₀, map_inv₀, heq, inv_one]
    exact ⟨⟨⟨ϖ, hϖP⟩, ⟨ϖ⁻¹, hinvP⟩, Subtype.ext (mul_inv_cancel₀ hϖ0), Subtype.ext (inv_mul_cancel₀ hϖ0)⟩, rfl⟩
  obtain ⟨πF, hπF, hπF2⟩ := exists_mem_not_mem_sq ((hQm.isPrime).under (𝓞 F)) h𝔭0
  have hvπF : P.valuation (algebraMap F (AlgebraicClosure ℚ) πF) = W := by
    simpa using hreadF πF 1 (by simpa using hπF) (by simpa using hπF2)
  have hπF0 : (πF : F) ≠ 0 := by
    intro h
    have : P.valuation (algebraMap F (AlgebraicClosure ℚ) πF) = 0 := by rw [h, map_zero, map_zero]
    exact hW0 (hvπF ▸ this)
  obtain ⟨k, hk⟩ := hfracF ϖ hϖ0
  have hk1 : k = 1 := by

    have hk1' : 1 ≤ k := by
      by_contra h
      have hk0 : k ≤ 0 := by omega
      have h1le : 1 ≤ W ^ k := by
        obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
        rw [hn, zpow_neg, zpow_natCast, one_le_inv₀ (pow_pos hWpos n)]
        exact pow_le_one₀ zero_le' hWlt.le
      exact absurd (hk ▸ hvϖlt) (not_lt.mpr h1le)
    by_contra hne
    have hk2 : 2 ≤ k := by omega
    set n : ℕ := (k - 1).toNat with hndef
    have hn : (n : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    have hn1 : n ≠ 0 := by omega

    have hvp : P.valuation (algebraMap F (AlgebraicClosure ℚ) ((πF : F) ^ n)) = W ^ n := by
      rw [map_pow, map_pow, hvπF]
    have hvt : P.valuation (algebraMap F (AlgebraicClosure ℚ) (ϖ / (πF : F) ^ n)) = W := by
      rw [map_div₀, map_div₀, hk, hvp, ← zpow_natCast, hn, ← zpow_sub₀ hW0]
      simp
    have htP : algebraMap F (AlgebraicClosure ℚ) (ϖ / (πF : F) ^ n) ∈ P :=
      (P.valuation_le_one_iff _).mp (hvt.le.trans hWlt.le)
    have hpP : algebraMap F (AlgebraicClosure ℚ) ((πF : F) ^ n) ∈ P :=
      (P.valuation_le_one_iff _).mp (hvp.le.trans (pow_le_one₀ zero_le' hWlt.le))
    have hprod : (⟨ϖ, hϖP⟩ : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ)))) =
        (⟨ϖ / (πF : F) ^ n, htP⟩ : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ)))) * ⟨(πF : F) ^ n, hpP⟩ := by
      apply Subtype.ext
      show ϖ = ϖ / (πF : F) ^ n * (πF : F) ^ n
      rw [div_mul_cancel₀ _ (pow_ne_zero n hπF0)]
    rcases hirr.isUnit_or_isUnit hprod with hu | hu
    · have := hunit _ hu
      change P.valuation (algebraMap F (AlgebraicClosure ℚ) (ϖ / (πF : F) ^ n)) = 1 at this
      rw [hvt] at this
      exact hWlt.ne this
    · have := hunit _ hu
      change P.valuation (algebraMap F (AlgebraicClosure ℚ) ((πF : F) ^ n)) = 1 at this
      rw [hvp] at this
      exact (pow_lt_one₀ zero_le' hWlt hn1).ne this
  have hvϖW : P.valuation (algebraMap F (AlgebraicClosure ℚ) ϖ) = W := by rw [hk, hk1, zpow_one]

  have hyE0 : (⟨y, hyE⟩ : ↥E) ≠ 0 := fun h => hy (congrArg Subtype.val h)
  obtain ⟨j, hj⟩ := hfracE ⟨y, hyE⟩ hyE0
  refine ⟨-j, ?_⟩
  rw [map_mul, map_zpow₀, hvϖW, show ((y : AlgebraicClosure ℚ)) = algebraMap ↥M (AlgebraicClosure ℚ) y from rfl,
    show (y : ↥M) = ((⟨y, hyE⟩ : ↥E) : ↥M) from rfl, hj, ← zpow_add₀ hW0, add_neg_cancel, zpow_zero]

end mainproof

end UVL

theorem solution
    (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (ϖ : F) (hϖP : algebraMap F (AlgebraicClosure ℚ) ϖ ∈ P)
    (hirr : Irreducible (⟨ϖ, hϖP⟩ : ↥(P.comap (algebraMap F (AlgebraicClosure ℚ)))))
    (M : IntermediateField F (AlgebraicClosure ℚ)) [FiniteDimensional F ↥M] [IsGalois F ↥M]
    (Q : Ideal (NumberField.RingOfIntegers ↥M)) [Q.IsMaximal]
    (hQle : ∀ x : NumberField.RingOfIntegers ↥M, P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) x) ≤ 1)
    (hQlt : ∀ x : NumberField.RingOfIntegers ↥M, x ∈ Q ↔ P.valuation (algebraMap ↥M (AlgebraicClosure ℚ) x) < 1)
    (y : ↥M) (hy : y ≠ 0)
    (hfix : ∀ τ : ↥M ≃ₐ[F] ↥M, τ ∈ Q.inertia (↥M ≃ₐ[F] ↥M) → τ y = y) :
    ∃ n : ℤ, P.valuation (((y : AlgebraicClosure ℚ)) * (algebraMap F (AlgebraicClosure ℚ) ϖ) ^ n) = 1 :=
  UVL.main F P q hP ϖ hϖP hirr M Q hQle hQlt y hy hfix

end S_ValuationSubring_exists_valuation_mul_zpow_eq_one_of_forall_inertia_apply_eq
end P2MW
export P2MW.S_ValuationSubring_exists_valuation_mul_zpow_eq_one_of_forall_inertia_apply_eq (solution)
