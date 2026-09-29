-- Prove2me | solution 1 for UniqueFactorizationMonoid.of_isLocalization_away_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/fb01eebe-ae55-5ee9-a7ac-acd353edc128

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UniqueFactorizationMonoid_of_isLocalization_away_of_prime

set_option autoImplicit false

namespace P2mNagata

open IsLocalization

variable {R : Type*} [CommRing R] [IsDomain R]

lemma pow_dvd_of_pow_dvd_mul_left {x r : R} (hx : Prime x) (hr : ¬x ∣ r) :
    ∀ (n : ℕ) (c : R), x ^ n ∣ r * c → x ^ n ∣ c := by
  intro n
  induction n with
  | zero => intro c _; simp
  | succ n ih =>
    intro c h
    have hxc : x ∣ c := by
      have : x ∣ r * c := (dvd_pow_self x n.succ_ne_zero).trans h
      exact (hx.dvd_or_dvd this).resolve_left hr
    obtain ⟨c', rfl⟩ := hxc
    rw [pow_succ, mul_left_comm] at h
    have h' : x ^ n ∣ r * c' := by
      obtain ⟨d, hd⟩ := h
      refine ⟨d, mul_left_cancel₀ hx.ne_zero ?_⟩
      rw [hd]; ring
    rw [pow_succ, mul_comm]
    exact mul_dvd_mul_left x (ih c' h')

variable {x : R} (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away x S]

lemma algebraMap_injective (hx0 : x ≠ 0) : Function.Injective (algebraMap R S) :=
  IsLocalization.injective S (M := Submonoid.powers x)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)

lemma prime_of_prime_algebraMap (hx : Prime x) {r₀ : R} (hr₀ : ¬x ∣ r₀) (hunit : ¬IsUnit r₀)
    (hprime : Prime (algebraMap R S r₀)) : Prime r₀ := by
  have hinj := algebraMap_injective S hx.ne_zero
  refine ⟨fun h => hprime.ne_zero (by rw [h, map_zero]), hunit, fun a b hab => ?_⟩

  have key : ∀ a : R, algebraMap R S r₀ ∣ algebraMap R S a → r₀ ∣ a := by
    intro a ⟨d, hd⟩
    obtain ⟨c, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers x) d
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : R) x).mp s.2

    have h1 : algebraMap R S (a * x ^ n) = algebraMap R S (r₀ * c) := by
      rw [map_mul, map_mul, hd, hn, mul_assoc, IsLocalization.mk'_spec]
    have h2 : a * x ^ n = r₀ * c := hinj h1
    have h3 : x ^ n ∣ r₀ * c := ⟨a, by rw [← h2, mul_comm]⟩
    obtain ⟨c', rfl⟩ := pow_dvd_of_pow_dvd_mul_left hx hr₀ n c h3
    refine ⟨c', mul_right_cancel₀ (pow_ne_zero n hx.ne_zero) ?_⟩
    rw [h2]; ring
  have : algebraMap R S r₀ ∣ algebraMap R S a * algebraMap R S b := by
    rw [← map_mul]; exact map_dvd (algebraMap R S) hab
  rcases hprime.dvd_or_dvd this with h | h
  · exact Or.inl (key a h)
  · exact Or.inr (key b h)

theorem main [IsNoetherianRing R] (hx : Prime x) [IsDomain S] [UniqueFactorizationMonoid S] :
    UniqueFactorizationMonoid R := by
  classical
  have hinj := algebraMap_injective S hx.ne_zero
  refine UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr fun P hP0 hP => ?_
  by_cases hxP : x ∈ P
  · exact ⟨x, hxP, hx⟩

  have hdisj : Disjoint (Submonoid.powers x : Set R) (P : Set R) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hxP (hP.mem_of_pow_mem n hn)
  have hPS : (P.map (algebraMap R S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x) S P hP hdisj
  have hPS0 : P.map (algebraMap R S) ≠ ⊥ := by
    intro h
    apply hP0
    rw [eq_bot_iff]
    intro r hr
    have : algebraMap R S r ∈ P.map (algebraMap R S) := Ideal.mem_map_of_mem _ hr
    rw [h, Ideal.mem_bot] at this
    exact (Ideal.mem_bot).mpr (hinj (by rw [this, map_zero]))
  obtain ⟨π, hπP, hπ⟩ :=
    (UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mp ‹_›) _ hPS0 hPS

  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers x) π
  have hunit_s : IsUnit (algebraMap R S s) := IsLocalization.map_units S s
  have hr_assoc : Associated (IsLocalization.mk' S r s) (algebraMap R S r) := by
    refine ⟨hunit_s.unit, ?_⟩
    rw [IsUnit.unit_spec, IsLocalization.mk'_spec]
  have hrS : Prime (algebraMap R S r) := hr_assoc.prime hπ
  have hrP : r ∈ P := by
    have hmem : algebraMap R S r ∈ P.map (algebraMap R S) := by
      have := Ideal.mul_mem_right (algebraMap R S s) _ hπP
      rwa [IsLocalization.mk'_spec] at this
    have : r ∈ (P.map (algebraMap R S)).under R := Ideal.mem_comap.mpr hmem
    rwa [IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers x) S hP hdisj] at this
  have hr0 : r ≠ 0 := fun h => hrS.ne_zero (by rw [h, map_zero])

  obtain ⟨e, r₀, hxr₀, rfl⟩ := WfDvdMonoid.max_power_factor' hr0 hx.not_unit
  have hr₀P : r₀ ∈ P :=
    (hP.mem_or_mem hrP).resolve_left fun h => hxP (hP.mem_of_pow_mem e h)
  have hr₀S : Prime (algebraMap R S r₀) := by
    have hassoc : Associated (algebraMap R S (x ^ e * r₀)) (algebraMap R S r₀) := by
      refine ⟨((IsLocalization.map_units S
        (⟨x ^ e, (Submonoid.mem_powers_iff _ _).mpr ⟨e, rfl⟩⟩ : Submonoid.powers x)).unit)⁻¹, ?_⟩
      rw [map_mul, mul_comm (algebraMap R S (x ^ e)), mul_assoc, IsUnit.mul_val_inv, mul_one]
    exact hassoc.prime hrS
  have hr₀unit : ¬IsUnit r₀ := fun h => hP.ne_top (P.eq_top_of_isUnit_mem hr₀P h)
  exact ⟨r₀, hr₀P, prime_of_prime_algebraMap S hx hxr₀ hr₀unit hr₀S⟩

end P2mNagata

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {x : R} (hx : Prime x)
    (S : Type*) [CommRing S] [IsDomain S] [Algebra R S] [IsLocalization.Away x S]
    [UniqueFactorizationMonoid S] : UniqueFactorizationMonoid R :=
  P2mNagata.main S hx

end S_UniqueFactorizationMonoid_of_isLocalization_away_of_prime
end P2MW
export P2MW.S_UniqueFactorizationMonoid_of_isLocalization_away_of_prime (solution)
