-- Prove2me | solution 1 for ValuationSubring.exists_uniform_pow_mul_mem_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ad896c8b-b797-5b40-89cc-cc9f5ec78334

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_uniform_pow_mul_mem_of_liesOverPrime

set_option autoImplicit false
set_option Elab.async false

namespace WindowDev

open IsLocalRing Polynomial

local notation "𝕂" => AlgebraicClosure ℚ

theorem inv_mem_of_isUnit_coe {K : Type*} [Field K] {A : ValuationSubring K} {x : A}
    (hx : IsUnit x) : ((x : K))⁻¹ ∈ A := by
  obtain ⟨u, hu⟩ := hx
  have h : ((x : A) : K) * (((u⁻¹ : Aˣ) : A) : K) = 1 := by
    have h0 : (u : A) * ((u⁻¹ : Aˣ) : A) = 1 := u.mul_inv
    rw [hu] at h0
    exact_mod_cast congrArg (fun z : A => (z : K)) h0
  rw [inv_eq_of_mul_eq_one_right h]
  exact Subtype.mem _

theorem inv_natCast_mem_of_not_dvd {A : ValuationSubring 𝕂} {p : ℕ} (hp : p.Prime)
    (hA : (p : 𝕂) ∈ A.nonunits) {m : ℕ} (hm : ¬ p ∣ m) : ((m : 𝕂))⁻¹ ∈ A := by
  obtain ⟨a, b, hab⟩ :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  have habK : (a : 𝕂) * p + b * m = 1 := by
    have h := congrArg (fun z : ℤ => (z : 𝕂)) hab
    push_cast at h
    exact h
  let P : A := ⟨(p : 𝕂), natCast_mem A p⟩
  let M : A := ⟨(m : 𝕂), natCast_mem A m⟩
  have hP : P ∈ maximalIdeal A := ValuationSubring.coe_mem_nonunits_iff.mp hA
  have hMu : IsUnit M := by
    by_contra hMu
    have hMm : M ∈ maximalIdeal A := (mem_maximalIdeal M).mpr (mem_nonunits_iff.mpr hMu)
    have hsum : (⟨(a : 𝕂), intCast_mem A a⟩ : A) * P + (⟨(b : 𝕂), intCast_mem A b⟩ : A) * M ∈
        maximalIdeal A :=
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ hP) (Ideal.mul_mem_left _ _ hMm)
    have h1 : (⟨(a : 𝕂), intCast_mem A a⟩ : A) * P + (⟨(b : 𝕂), intCast_mem A b⟩ : A) * M = 1 := by
      apply Subtype.ext
      push_cast
      exact habK
    rw [h1] at hsum
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr hsum)
  exact inv_mem_of_isUnit_coe hMu

theorem aeval_int_mem (A : ValuationSubring 𝕂) {c : 𝕂} (hc : c ∈ A) (q : ℤ[X]) :
    aeval c q ∈ A := by
  refine Polynomial.induction_on' q ?_ ?_
  · intro f g hf hg
    rw [map_add]
    exact add_mem hf hg
  · intro n a
    rw [aeval_monomial, eq_intCast]
    exact mul_mem (intCast_mem A a) (pow_mem hc n)

theorem exists_intCast_mul_inv_mem {A : ValuationSubring 𝕂} {c : 𝕂} (hc : c ∈ A) (hc0 : c ≠ 0) :
    ∃ b : ℤ, b ≠ 0 ∧ (b : 𝕂) * c⁻¹ ∈ A := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ 𝕂).mpr ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic c)
  obtain ⟨f, hf0, hfc⟩ := halg
  obtain ⟨g, hfg, hXg⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
  have hg0 : g.coeff 0 ≠ 0 := by
    intro h
    apply hXg
    rw [map_zero, sub_zero]
    exact X_dvd_iff.mpr h
  have hgc : aeval c g = 0 := by
    have h := hfc
    rw [hfg, map_mul, map_pow, map_sub, aeval_X, aeval_C, map_zero, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hc0)
  have key : (g.coeff 0 : 𝕂) * c⁻¹ = -(aeval c g.divX) := by
    have h := congrArg (aeval c) (X_mul_divX_add g)
    rw [map_add, map_mul, aeval_X, aeval_C, hgc, eq_intCast] at h

    field_simp
    linear_combination h
  exact ⟨g.coeff 0, hg0, key ▸ neg_mem (aeval_int_mem A hc g.divX)⟩

theorem exists_window {A : ValuationSubring 𝕂} {p : ℕ} (hp : p.Prime)
    (hA : (p : 𝕂) ∈ A.nonunits) {c : 𝕂} (hc0 : c ≠ 0) :
    ∃ B : ℕ, (p : 𝕂) ^ B * c ∈ A ∧ (p : 𝕂) ^ B * c⁻¹ ∈ A := by

  have step : ∀ {x : 𝕂}, x ∈ A → x ≠ 0 → ∃ B : ℕ, (p : 𝕂) ^ B * x⁻¹ ∈ A := by
    intro x hx hx0
    obtain ⟨b, hb0, hb⟩ := exists_intCast_mul_inv_mem hx hx0
    have hbn0 : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb0
    obtain ⟨B, m, hm, hbm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hbn0 p hp.ne_one
    obtain ⟨u, hu⟩ := Int.dvd_natAbs.mpr (dvd_refl b)

    have hnat : (b.natAbs : 𝕂) * x⁻¹ ∈ A := by
      have : (b.natAbs : 𝕂) * x⁻¹ = (u : 𝕂) * ((b : 𝕂) * x⁻¹) := by
        rw [← Int.cast_natCast, hu]; push_cast; ring
      rw [this]
      exact mul_mem (intCast_mem A u) hb
    have hm0 : (m : 𝕂) ≠ 0 := by
      intro h
      rw [Nat.cast_eq_zero] at h
      rw [h, mul_zero] at hbm
      exact hbn0 hbm
    refine ⟨B, ?_⟩
    have : (p : 𝕂) ^ B * x⁻¹ = ((m : 𝕂))⁻¹ * ((b.natAbs : 𝕂) * x⁻¹) := by
      rw [hbm]; push_cast; field_simp
    rw [this]
    exact mul_mem (inv_natCast_mem_of_not_dvd hp hA hm) hnat
  have hpA : (p : 𝕂) ∈ A := natCast_mem A p
  rcases A.mem_or_inv_mem c with hc | hc
  · obtain ⟨B, hB⟩ := step hc hc0
    exact ⟨B, mul_mem (pow_mem hpA B) hc, hB⟩
  · obtain ⟨B, hB⟩ := step hc (inv_ne_zero hc0)
    rw [inv_inv] at hB
    exact ⟨B, hB, mul_mem (pow_mem hpA B) hc⟩

theorem window_mono {A : ValuationSubring 𝕂} {p : ℕ} {c : 𝕂} {B B' : ℕ} (h : B ≤ B')
    (hB : (p : 𝕂) ^ B * c ∈ A) : (p : 𝕂) ^ B' * c ∈ A := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_assoc]
  exact mul_mem (pow_mem (natCast_mem A p) _) hB

theorem mem_of_isIntegral_int (A : ValuationSubring 𝕂) {y : 𝕂} (hy : IsIntegral ℤ y) : y ∈ A := by
  obtain ⟨f, hfm, hf⟩ := hy
  have hA : IsIntegral A y := by
    refine ⟨f.map (algebraMap ℤ A), hfm.map _, ?_⟩
    rw [eval₂_map, RingHom.ext_int ((algebraMap A 𝕂).comp (algebraMap ℤ A)) (algebraMap ℤ 𝕂)]
    exact hf
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := 𝕂)).mp hA
  rw [← hz]
  exact z.2

theorem exists_intCast_mul_inv_eq_aeval {y : 𝕂} (hy0 : y ≠ 0) :
    ∃ b : ℤ, b ≠ 0 ∧ ∃ r : ℤ[X], (b : 𝕂) * y⁻¹ = aeval y r := by
  have halg : IsAlgebraic ℤ y :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ 𝕂).mpr ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y)
  obtain ⟨f, hf0, hfc⟩ := halg
  obtain ⟨g, hfg, hXg⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
  have hg0 : g.coeff 0 ≠ 0 := by
    intro h
    apply hXg
    rw [map_zero, sub_zero]
    exact X_dvd_iff.mpr h
  have hgc : aeval y g = 0 := by
    have h := hfc
    rw [hfg, map_mul, map_pow, map_sub, aeval_X, aeval_C, map_zero, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hy0)
  refine ⟨g.coeff 0, hg0, -g.divX, ?_⟩
  have h := congrArg (aeval y) (X_mul_divX_add g)
  rw [map_add, map_mul, aeval_X, aeval_C, hgc, eq_intCast] at h
  rw [map_neg]
  field_simp
  linear_combination h

theorem exists_pow_mul_intCast_inv_mem {p : ℕ} (hp : p.Prime) {n : ℤ} (hn : n ≠ 0) :
    ∃ i : ℕ, ∀ A : ValuationSubring 𝕂, (p : 𝕂) ∈ A.nonunits → (p : 𝕂) ^ i * ((n : 𝕂))⁻¹ ∈ A := by
  have hn0 : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  obtain ⟨i, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
  obtain ⟨u, hu⟩ := Int.dvd_natAbs.mpr (dvd_refl n)
  refine ⟨i, fun A hA => ?_⟩
  have hm0 : (m : 𝕂) ≠ 0 := by
    intro h
    rw [Nat.cast_eq_zero] at h
    rw [h, mul_zero] at hnm
    exact hn0 hnm
  have hnK : (n : 𝕂) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hcast : (n : 𝕂) * (u : 𝕂) = (p : 𝕂) ^ i * (m : 𝕂) := by
    have h1 : ((n.natAbs : ℤ) : 𝕂) = (n : 𝕂) * (u : 𝕂) := by rw [hu, Int.cast_mul]
    rw [Int.cast_natCast, hnm, Nat.cast_mul, Nat.cast_pow] at h1
    exact h1.symm
  have : (p : 𝕂) ^ i * ((n : 𝕂))⁻¹ = (u : 𝕂) * ((m : 𝕂))⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff hnK hm0]
    linear_combination -hcast
  rw [this]
  exact mul_mem (intCast_mem A u) (inv_natCast_mem_of_not_dvd hp hA hm)

theorem exists_uniform_window {p : ℕ} (hp : p.Prime) {x : 𝕂} (hx : x ≠ 0) :
    ∃ B : ℕ, ∀ A : ValuationSubring 𝕂, (p : 𝕂) ∈ A.nonunits →
      (p : 𝕂) ^ B * x ∈ A ∧ (p : 𝕂) ^ B * x⁻¹ ∈ A := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ 𝕂).mpr ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x)
  obtain ⟨d, hd0, hdx⟩ := halg.exists_integral_multiple
  rw [Algebra.smul_def, eq_intCast] at hdx
  set y : 𝕂 := (d : 𝕂) * x with hy
  have hdK : (d : 𝕂) ≠ 0 := Int.cast_ne_zero.mpr hd0
  have hy0 : y ≠ 0 := mul_ne_zero hdK hx
  obtain ⟨b, hb0, r, hbr⟩ := exists_intCast_mul_inv_eq_aeval hy0
  obtain ⟨i, hi⟩ := exists_pow_mul_intCast_inv_mem hp hd0
  obtain ⟨j, hj⟩ := exists_pow_mul_intCast_inv_mem hp hb0
  refine ⟨i + j, fun A hA => ?_⟩
  have hyA : y ∈ A := mem_of_isIntegral_int A hdx
  have hbyA : (b : 𝕂) * y⁻¹ ∈ A := by rw [hbr]; exact aeval_int_mem A hyA r
  have hpA : (p : 𝕂) ∈ A := natCast_mem A p
  have hbK : (b : 𝕂) ≠ 0 := Int.cast_ne_zero.mpr hb0
  have hdd : ((d : 𝕂))⁻¹ * (d : 𝕂) = 1 := inv_mul_cancel₀ hdK
  have hbb : ((b : 𝕂))⁻¹ * (b : 𝕂) = 1 := inv_mul_cancel₀ hbK
  have hxinv : x⁻¹ = (d : 𝕂) * y⁻¹ := by
    rw [hy, mul_inv, ← mul_assoc, mul_inv_cancel₀ hdK, one_mul]
  constructor
  · have : (p : 𝕂) ^ (i + j) * x = (p : 𝕂) ^ j * (((p : 𝕂) ^ i * ((d : 𝕂))⁻¹) * y) := by
      rw [hy]
      linear_combination (-((p : 𝕂) ^ (i + j) * x)) * hdd
    rw [this]
    exact mul_mem (pow_mem hpA j) (mul_mem (hi A hA) hyA)
  · have : (p : 𝕂) ^ (i + j) * x⁻¹
        = (p : 𝕂) ^ i * ((d : 𝕂) * (((p : 𝕂) ^ j * ((b : 𝕂))⁻¹) * ((b : 𝕂) * y⁻¹))) := by
      rw [hxinv]
      linear_combination (-((p : 𝕂) ^ (i + j) * (d : 𝕂) * y⁻¹)) * hbb
    rw [this]
    exact mul_mem (pow_mem hpA i) (mul_mem (intCast_mem A d) (mul_mem (hj A hA) hbyA))

end WindowDev

theorem solution {p : ℕ} (hp : p.Prime)
    {x : AlgebraicClosure ℚ} (hx : x ≠ 0) :
    ∃ B : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      (p : AlgebraicClosure ℚ) ^ B * x ∈ A ∧ (p : AlgebraicClosure ℚ) ^ B * x⁻¹ ∈ A := by
  obtain ⟨B, hB⟩ := WindowDev.exists_uniform_window hp hx
  exact ⟨B, fun A hA => hB A hA⟩

end S_ValuationSubring_exists_uniform_pow_mul_mem_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_exists_uniform_pow_mul_mem_of_liesOverPrime (solution)
