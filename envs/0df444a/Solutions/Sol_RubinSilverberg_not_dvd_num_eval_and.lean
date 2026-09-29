-- Prove2me | solution 1 for RubinSilverberg.not_dvd_num_eval_and
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8c608279-09d8-5a3d-9c63-8402f5055b00

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Data.Nat.Prime.Int
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_not_dvd_num_eval_and

namespace RubinSilverberg
p2m_export "RubinSilverberg" "kleinV kleinH kleinT kleinHHom kleinTHom rsBeta rsGamma rsNum rsDen rsFamilyA rsFamilyB IsKleinDatum"
p2m_open "RubinSilverberg"

open Polynomial

section Bezout

variable {R : Type*} [CommRing R]

theorem map_kleinH {S : Type*} [CommRing S] (f : R →+* S) (u : R) : f (kleinH u) = kleinH (f u) := by
  simp [kleinH, map_ofNat]

theorem map_kleinV {S : Type*} [CommRing S] (f : R →+* S) (u : R) : f (kleinV u) = kleinV (f u) := by
  simp [kleinV, map_ofNat]

theorem map_kleinT {S : Type*} [CommRing S] (f : R →+* S) (u : R) : f (kleinT u) = kleinT (f u) := by
  simp [kleinT, map_ofNat]

theorem bezout_kleinH_kleinV_s10 (u : R) :
    (3125 - 33022 * u ^ 5 - 3003 * u ^ 10) * kleinH u +
      (679478 * u ^ 4 + 1485989 * u ^ 9 - 684695 * u ^ 14 + 3003 * u ^ 19) * kleinV u = 3125 := by
  unfold kleinH kleinV
  ring

theorem bezout_kleinH_kleinT_s10 (u : R) :
    (950431323 + 20237705983 * u ^ 5 - 103588896 * u ^ 10 + 20237108822 * u ^ 15
        - 1055557719 * u ^ 20 - 2022161 * u ^ 25) * kleinH u +
      (455818677 + 1001301767 * u ^ 5 - 461063031 * u ^ 10 + 2022161 * u ^ 15) * kleinT u =
      1406250000 := by
  unfold kleinH kleinT
  ring

theorem kleinT_sq_sub_kleinH_cube' (u : R) : kleinT u ^ 2 - kleinH u ^ 3 = 1728 * kleinV u ^ 5 := by
  unfold kleinT kleinH kleinV
  ring

theorem natDegree_kleinH_X_le [Nontrivial R] : (kleinH (X : R[X])).natDegree ≤ 20 := by
  unfold kleinH
  compute_degree

theorem coeff_kleinH_X [Nontrivial R] : (kleinH (X : R[X])).coeff 20 = 1 := by
  unfold kleinH
  simp [coeff_X_pow, coeff_one, ← C_ofNat, coeff_C_mul]

theorem natDegree_kleinV_X_le [Nontrivial R] : (kleinV (X : R[X])).natDegree ≤ 11 := by
  unfold kleinV
  compute_degree

end Bezout

section Datum

variable {K : Type*} [Field K]

theorem IsKleinDatum.kleinH_ne_zero_s10 [CharZero K] {a b u₀ : K} (h : IsKleinDatum a b u₀) (ha : a ≠ 0) :
    kleinH u₀ ≠ 0 := by
  intro hH
  obtain ⟨heq, hV⟩ := h
  rw [hH, zero_pow three_ne_zero, zero_mul, zero_add] at heq
  have : (6912 : K) ≠ 0 := by norm_num
  exact hV (eq_zero_of_pow_eq_zero (eq_zero_of_ne_zero_of_mul_left_eq_zero (mul_ne_zero this (pow_ne_zero 3 ha)) heq))

theorem IsKleinDatum.disc_ne_zero_s10 [CharZero K] {a b u₀ : K} (h : IsKleinDatum a b u₀) (ha : a ≠ 0) :
    4 * a ^ 3 + 27 * b ^ 2 ≠ 0 := by
  intro hD
  obtain ⟨heq, hV⟩ := h
  rw [hD, mul_zero, zero_add] at heq
  have : (6912 : K) ≠ 0 := by norm_num
  exact hV (eq_zero_of_pow_eq_zero (eq_zero_of_ne_zero_of_mul_left_eq_zero (mul_ne_zero this (pow_ne_zero 3 ha)) heq))

namespace IsKleinDatum

private theorem _root_.RubinSilverberg.IsKleinDatum.kleinT_sq_mul {a b u₀ : K} (h : IsKleinDatum a b u₀) :
    kleinT u₀ ^ 2 * (4 * a ^ 3 + 27 * b ^ 2) = 46656 * b ^ 2 * kleinV u₀ ^ 5 := by
  have hs := kleinT_sq_sub_kleinH_cube' u₀
  linear_combination (4 * a ^ 3 + 27 * b ^ 2) * hs + h.1

end IsKleinDatum
p2m_export "RubinSilverberg" "IsKleinDatum.kleinT_sq_mul"

theorem IsKleinDatum.kleinT_ne_zero_s10 [CharZero K] {a b u₀ : K} (h : IsKleinDatum a b u₀) (hb : b ≠ 0) :
    kleinT u₀ ≠ 0 := by
  intro hT
  have heq := h.kleinT_sq_mul
  rw [hT, zero_pow two_ne_zero, zero_mul] at heq
  have : (46656 : K) ≠ 0 := by norm_num
  exact h.2 (eq_zero_of_pow_eq_zero
    (eq_zero_of_ne_zero_of_mul_left_eq_zero (mul_ne_zero this (pow_ne_zero 2 hb)) heq.symm))

theorem exists_isKleinDatum_s10 [IsAlgClosed K] [CharZero K] (a b : K)
    (hD : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) : ∃ u₀ : K, IsKleinDatum a b u₀ := by

  set P : K[X] := C (4 * a ^ 3 + 27 * b ^ 2) * kleinH X ^ 3 + C (6912 * a ^ 3) * kleinV X ^ 5 with hP
  have hcoeff : P.coeff 60 = 4 * a ^ 3 + 27 * b ^ 2 := by
    have h1 : (kleinH (X : K[X]) ^ 3).coeff 60 = 1 := by
      have := coeff_pow_of_natDegree_le (natDegree_kleinH_X_le (R := K)) (m := 3)
      rw [show 3 * 20 = 60 from rfl, coeff_kleinH_X, one_pow] at this
      exact this
    have h2 : (kleinV (X : K[X]) ^ 5).coeff 60 = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      calc (kleinV (X : K[X]) ^ 5).natDegree ≤ 5 * (kleinV (X : K[X])).natDegree := natDegree_pow_le
        _ ≤ 5 * 11 := Nat.mul_le_mul_left 5 natDegree_kleinV_X_le
        _ < 60 := by norm_num
    rw [hP, coeff_add, coeff_C_mul, coeff_C_mul, h1, h2, mul_one, mul_zero, add_zero]
  have hdeg : P.degree ≠ 0 := by
    intro h0
    have h60 : 60 ≤ P.natDegree := le_natDegree_of_ne_zero (by rw [hcoeff]; exact hD)
    have := natDegree_eq_zero_iff_degree_le_zero.mpr h0.le
    omega
  obtain ⟨u₀, hu₀⟩ := IsAlgClosed.exists_root P hdeg
  have heval : kleinH u₀ ^ 3 * (4 * a ^ 3 + 27 * b ^ 2) + 6912 * a ^ 3 * kleinV u₀ ^ 5 = 0 := by
    have h := hu₀
    rw [IsRoot.def, hP, eval_add, eval_mul, eval_mul, eval_C, eval_C, eval_pow, eval_pow,
      ← coe_evalRingHom, map_kleinH, map_kleinV, coe_evalRingHom, eval_X] at h
    linear_combination h
  refine ⟨u₀, heval, fun hV ↦ ?_⟩

  have hH : kleinH u₀ = 0 := by
    rw [hV, zero_pow (by norm_num), mul_zero, add_zero] at heval
    exact eq_zero_of_pow_eq_zero (eq_zero_of_ne_zero_of_mul_right_eq_zero hD heval)
  have hbez := bezout_kleinH_kleinV_s10 u₀
  rw [hH, hV, mul_zero, mul_zero, add_zero] at hbez
  norm_num at hbez

end Datum

end RubinSilverberg

namespace RubinSilverberg
p2m_export "RubinSilverberg" "kleinV kleinH kleinT kleinHHom kleinTHom rsBeta rsGamma rsNum rsDen rsFamilyA rsFamilyB IsKleinDatum"
p2m_open "RubinSilverberg"

open Polynomial IsDedekindDomain

section FormsAlgebra

variable {R : Type*} [CommRing R]

theorem map_kleinHHom {S : Type*} [CommRing S] (f : R →+* S) (n d : R) :
    f (kleinHHom n d) = kleinHHom (f n) (f d) := by
  simp [kleinHHom, map_ofNat]

theorem map_kleinTHom {S : Type*} [CommRing S] (f : R →+* S) (n d : R) :
    f (kleinTHom n d) = kleinTHom (f n) (f d) := by
  simp [kleinTHom, map_ofNat]

def kleinF (u : R) : R := u ^ 10 + 11 * u ^ 5 - 1

theorem kleinV_eq_mul_kleinF (u : R) : kleinV u = u * kleinF u := rfl

theorem map_kleinF {S : Type*} [CommRing S] (f : R →+* S) (u : R) : f (kleinF u) = kleinF (f u) := by
  simp [kleinF, map_ofNat]

def bezHVa (u : R) : R := 3125 - 33022 * u ^ 5 - 3003 * u ^ 10
def bezHVb (u : R) : R := 679478 * u ^ 4 + 1485989 * u ^ 9 - 684695 * u ^ 14 + 3003 * u ^ 19
def bezHTa (u : R) : R := 950431323 + 20237705983 * u ^ 5 - 103588896 * u ^ 10
  + 20237108822 * u ^ 15 - 1055557719 * u ^ 20 - 2022161 * u ^ 25
def bezHTb (u : R) : R := 455818677 + 1001301767 * u ^ 5 - 461063031 * u ^ 10 + 2022161 * u ^ 15

theorem map_bezHVa {S : Type*} [CommRing S] (f : R →+* S) (u : R) : f (bezHVa u) = bezHVa (f u) := by
  simp [bezHVa, map_ofNat]
theorem map_bezHVb {S : Type*} [CommRing S] (f : R →+* S) (u : R) : f (bezHVb u) = bezHVb (f u) := by
  simp [bezHVb, map_ofNat]
theorem map_bezHTa {S : Type*} [CommRing S] (f : R →+* S) (u : R) : f (bezHTa u) = bezHTa (f u) := by
  simp [bezHTa, map_ofNat]
theorem map_bezHTb {S : Type*} [CommRing S] (f : R →+* S) (u : R) : f (bezHTb u) = bezHTb (f u) := by
  simp [bezHTb, map_ofNat]

theorem bezout_HV (u : R) : bezHVa u * kleinH u + bezHVb u * kleinV u = 3125 :=
  bezout_kleinH_kleinV_s10 u

theorem bezout_HT (u : R) : bezHTa u * kleinH u + bezHTb u * kleinT u = 1406250000 := by
  unfold bezHTa bezHTb
  exact bezout_kleinH_kleinT_s10 u

def kleinHTail (n d : R) : R := -228 * n ^ 15 * d ^ 4 + 494 * n ^ 10 * d ^ 9 + 228 * n ^ 5 * d ^ 14 + d ^ 19

theorem kleinHHom_eq_add_tail (n d : R) : kleinHHom n d = n ^ 20 + d * kleinHTail n d := by
  unfold kleinHHom kleinHTail
  ring

theorem map_kleinHTail {S : Type*} [CommRing S] (f : R →+* S) (n d : R) :
    f (kleinHTail n d) = kleinHTail (f n) (f d) := by
  simp [kleinHTail, map_ofNat]

def rsBetaNum (u : R) : R := 57 * u ^ 15 - 247 * u ^ 10 - 171 * u ^ 5 - 1
def rsGammaNum (u : R) : R := u ^ 15 - 171 * u ^ 10 + 247 * u ^ 5 + 57

theorem map_rsBetaNum {S : Type*} [CommRing S] (f : R →+* S) (u : R) : f (rsBetaNum u) = rsBetaNum (f u) := by
  simp [rsBetaNum, map_ofNat]
theorem map_rsGammaNum {S : Type*} [CommRing S] (f : R →+* S) (u : R) : f (rsGammaNum u) = rsGammaNum (f u) := by
  simp [rsGammaNum, map_ofNat]

end FormsAlgebra

section FieldAlgebra

variable {K : Type*} [Field K]

theorem rsBeta_eq (u : K) : rsBeta u = kleinT u * rsBetaNum u / (144 * u ^ 4 * kleinF u ^ 4) := rfl
theorem rsGamma_eq (u : K) : rsGamma u = kleinT u * rsGammaNum u / (144 * kleinF u ^ 4) := rfl

theorem map_rsBeta {L : Type*} [Field L] (f : K →+* L) (u : K) : f (rsBeta u) = rsBeta (f u) := by
  rw [rsBeta_eq, rsBeta_eq, map_div₀, map_mul, map_mul, map_mul, map_pow, map_pow, map_kleinT, map_kleinF,
    map_rsBetaNum, map_ofNat]

theorem map_rsGamma {L : Type*} [Field L] (f : K →+* L) (u : K) : f (rsGamma u) = rsGamma (f u) := by
  rw [rsGamma_eq, rsGamma_eq, map_div₀, map_mul, map_mul, map_pow, map_kleinT, map_kleinF, map_rsGammaNum,
    map_ofNat]

theorem rsBeta_sub_mul_rsGamma (u : K) (hu : u ≠ 0) (hF : kleinF u ≠ 0) :
    rsBeta u - u * rsGamma u = -(kleinT u * kleinH u) / (144 * u ^ 4 * kleinF u ^ 4) := by
  rw [rsBeta_eq, rsGamma_eq]
  unfold rsBetaNum rsGammaNum kleinH
  field_simp
  ring

theorem kleinHHom_eq_pow_mul (n d : K) (hd : d ≠ 0) : kleinHHom n d = d ^ 20 * kleinH (n / d) := by
  unfold kleinHHom kleinH
  field_simp

theorem kleinTHom_eq_pow_mul (n d : K) (hd : d ≠ 0) : kleinTHom n d = d ^ 30 * kleinT (n / d) := by
  unfold kleinTHom kleinT
  field_simp

noncomputable def polyA (a u₀ l : K) : K[X] :=
  C (a / kleinH u₀) * kleinHHom (C (rsBeta u₀ + l * u₀) * X + C u₀) (C (rsGamma u₀ + l) * X + 1)

noncomputable def polyB (b u₀ l : K) : K[X] :=
  C (b / kleinT u₀) * kleinTHom (C (rsBeta u₀ + l * u₀) * X + C u₀) (C (rsGamma u₀ + l) * X + 1)

theorem eval_polyA (a u₀ l t : K) : (polyA a u₀ l).eval t = rsFamilyA a u₀ l t := by
  rw [polyA, eval_mul, eval_C, ← coe_evalRingHom, map_kleinHHom]
  simp only [coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, eval_one]
  rw [rsFamilyA, rsNum, rsDen]
  ring

theorem eval_polyB (b u₀ l t : K) : (polyB b u₀ l).eval t = rsFamilyB b u₀ l t := by
  rw [polyB, eval_mul, eval_C, ← coe_evalRingHom, map_kleinTHom]
  simp only [coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, eval_one]
  rw [rsFamilyB, rsNum, rsDen]
  ring

theorem map_polyA {L : Type*} [Field L] (f : K →+* L) (a u₀ l : K) :
    (polyA a u₀ l).map f = polyA (f a) (f u₀) (f l) := by
  rw [polyA, polyA, Polynomial.map_mul, map_C, ← coe_mapRingHom, map_kleinHHom]
  simp [map_rsBeta, map_rsGamma, map_div₀, map_kleinH]

theorem map_polyB {L : Type*} [Field L] (f : K →+* L) (b u₀ l : K) :
    (polyB b u₀ l).map f = polyB (f b) (f u₀) (f l) := by
  rw [polyB, polyB, Polynomial.map_mul, map_C, ← coe_mapRingHom, map_kleinTHom]
  simp [map_rsBeta, map_rsGamma, map_div₀, map_kleinT]

theorem isKleinDatum_map_iff {L : Type*} [Field L] (f : K →+* L) (a b u : K) :
    IsKleinDatum (f a) (f b) (f u) ↔ IsKleinDatum a b u := by
  unfold IsKleinDatum
  rw [← map_kleinH f, ← map_kleinV f, (map_ne_zero f)]
  refine and_congr_left fun _ ↦ ?_
  rw [← map_eq_zero_iff f f.injective]
  simp [map_ofNat]

end FieldAlgebra

end RubinSilverberg

open Polynomial IsDedekindDomain

namespace RubinSilverberg
p2m_export "RubinSilverberg" "kleinV kleinH kleinT kleinHHom kleinTHom rsBeta rsGamma rsNum rsDen rsFamilyA rsFamilyB IsKleinDatum"
namespace Val
p2m_open "RubinSilverberg"

section Root

variable {L Γ₀ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation L Γ₀)

theorem le_one_of_isRoot {P : L[X]} (hcoeff : ∀ i, w (P.coeff i) ≤ 1)
    (hlead : w P.leadingCoeff = 1) {x : L} (hx : P.IsRoot x) : w x ≤ 1 := by
  by_contra hgt
  push Not at hgt
  have hx0 : x ≠ 0 := by rintro rfl; simp at hgt
  have hwx : w x ≠ 0 := (Valuation.ne_zero_iff w).mpr hx0
  set n := P.natDegree with hn
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hlead

  have hsplit : P.eval x = P.leadingCoeff * x ^ n + ∑ i ∈ Finset.range n, P.coeff i * x ^ i := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, add_comm]
    rfl
  have htop : w (P.leadingCoeff * x ^ n) = w x ^ n := by
    rw [map_mul, map_pow, hlead, one_mul]
  have hrest : w (∑ i ∈ Finset.range n, P.coeff i * x ^ i) < w x ^ n := by
    apply Valuation.map_sum_lt w (pow_ne_zero n hwx)
    intro i hi
    rw [Finset.mem_range] at hi
    calc w (P.coeff i * x ^ i) = w (P.coeff i) * w x ^ i := by rw [map_mul, map_pow]
      _ ≤ 1 * w x ^ i := by gcongr; exact hcoeff i
      _ = w x ^ i := one_mul _
      _ < w x ^ n := pow_lt_pow_right₀ hgt hi
  have hval : w (P.eval x) = w x ^ n := by
    rw [hsplit, Valuation.map_add_eq_of_lt_left w (by rwa [htop]), htop]
  rw [hx.eq_zero, map_zero] at hval
  exact pow_ne_zero n hwx hval.symm

theorem coeff_le_one_iff_mem_lifts (P : L[X]) :
    (∀ i, w (P.coeff i) ≤ 1) ↔ P ∈ Polynomial.liftsRing w.integer.subtype := by
  rw [liftsRing, RingHom.mem_range]
  constructor
  · intro h
    refine ⟨∑ i ∈ P.support, C ⟨P.coeff i, h i⟩ * X ^ i, ?_⟩
    conv_rhs => rw [P.as_sum_support_C_mul_X_pow]
    simp
  · rintro ⟨Q, rfl⟩ i
    rw [coe_mapRingHom, coeff_map]
    exact (Q.coeff i).2

end Root

section Rational

variable {F : Type*} [Field F] [NumberField F]

open NumberField

theorem exists_heightOneSpectrum_over (p : ℕ) (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 F), v.asIdeal.comap (algebraMap ℤ (𝓞 F)) = Ideal.span {(p : ℤ)} := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨Q, hQprime, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F)
    (Ideal.span {(p : ℤ)}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 F)).injective_int]
      exact bot_le)
  refine ⟨⟨Q, hQprime, ?_⟩, hQ⟩
  rintro rfl
  rw [Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 F)).injective_int] at hQ
  exact (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0) (Ideal.span_singleton_eq_bot.mp hQ.symm)

variable (v : HeightOneSpectrum (𝓞 F)) {p : ℕ}

theorem valuation_intCast_lt_one_iff (hv : v.asIdeal.comap (algebraMap ℤ (𝓞 F)) = Ideal.span {(p : ℤ)})
    (n : ℤ) : v.valuation F (n : F) < 1 ↔ (p : ℤ) ∣ n := by
  have : (n : F) = algebraMap (𝓞 F) F (n : 𝓞 F) := by simp
  rw [this, HeightOneSpectrum.valuation_lt_one_iff_dvd, Ideal.dvd_span_singleton,
    ← Ideal.mem_span_singleton, ← hv, Ideal.mem_comap]
  simp

theorem valuation_intCast_le_one (n : ℤ) : v.valuation F (n : F) ≤ 1 := by
  have : (n : F) = algebraMap (𝓞 F) F (n : 𝓞 F) := by simp
  rw [this]
  exact HeightOneSpectrum.valuation_le_one v _

theorem valuation_intCast_eq_one_iff (hv : v.asIdeal.comap (algebraMap ℤ (𝓞 F)) = Ideal.span {(p : ℤ)})
    (n : ℤ) : v.valuation F (n : F) = 1 ↔ ¬ (p : ℤ) ∣ n := by
  rw [← valuation_intCast_lt_one_iff v hv n, not_lt]
  exact ⟨fun h ↦ h.ge, fun h ↦ le_antisymm (valuation_intCast_le_one v n) h⟩

theorem not_dvd_den_of_valuation_le_one (hv : v.asIdeal.comap (algebraMap ℤ (𝓞 F)) = Ideal.span {(p : ℤ)})
    (hp : p.Prime) {q : ℚ} (hq : v.valuation F (q : F) ≤ 1) : ¬ p ∣ q.den := by
  intro hden
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hnum
    have := Int.natAbs_dvd_natAbs.mpr hnum
    rw [Int.natAbs_natCast] at this
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one (q.reduced ▸ Nat.dvd_gcd this hden))
  have hq' : (q : F) = (q.num : F) / (q.den : F) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hden' : v.valuation F ((q.den : ℤ) : F) < 1 :=
    (valuation_intCast_lt_one_iff v hv _).mpr (by exact_mod_cast hden)
  have hnum' : v.valuation F (q.num : F) = 1 := (valuation_intCast_eq_one_iff v hv _).mpr hnum
  have hden0 : v.valuation F ((q.den : ℤ) : F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (by exact_mod_cast q.den_ne_zero)
  rw [hq', map_div₀, hnum', show ((q.den : F)) = ((q.den : ℤ) : F) by simp] at hq
  rw [one_div, inv_le_one₀ (zero_lt_iff.mpr hden0)] at hq
  exact absurd hq (not_le.mpr hden')

theorem valuation_lt_one_iff_dvd_num (hv : v.asIdeal.comap (algebraMap ℤ (𝓞 F)) = Ideal.span {(p : ℤ)})
    {q : ℚ} (hden : ¬ p ∣ q.den) : v.valuation F (q : F) < 1 ↔ (p : ℤ) ∣ q.num := by
  have hq' : (q : F) = (q.num : F) / ((q.den : ℤ) : F) := by
    rw [Int.cast_natCast, ← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hden1 : v.valuation F ((q.den : ℤ) : F) = 1 :=
    (valuation_intCast_eq_one_iff v hv _).mpr (by exact_mod_cast hden)
  rw [hq', map_div₀, hden1, div_one]
  exact valuation_intCast_lt_one_iff v hv _

theorem valuation_le_one_of_not_dvd_den (hv : v.asIdeal.comap (algebraMap ℤ (𝓞 F)) = Ideal.span {(p : ℤ)})
    {q : ℚ} (hden : ¬ p ∣ q.den) : v.valuation F (q : F) ≤ 1 := by
  have hq' : (q : F) = (q.num : F) / ((q.den : ℤ) : F) := by
    rw [Int.cast_natCast, ← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hden1 : v.valuation F ((q.den : ℤ) : F) = 1 :=
    (valuation_intCast_eq_one_iff v hv _).mpr (by exact_mod_cast hden)
  rw [hq', map_div₀, hden1, div_one]
  exact valuation_intCast_le_one v _

end Rational

end RubinSilverberg.Val

namespace RubinSilverberg
p2m_export "RubinSilverberg" "kleinV kleinH kleinT kleinHHom kleinTHom rsBeta rsGamma rsNum rsDen rsFamilyA rsFamilyB IsKleinDatum"
p2m_open "RubinSilverberg"

open Polynomial IsDedekindDomain

section OrderAux

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

private theorem mul_lt_one_of_le_of_lt₀ {x y : Γ₀} (hx : x ≤ 1) (hy : y < 1) : x * y < 1 :=
  calc x * y ≤ 1 * y := by gcongr
    _ = y := one_mul y
    _ < 1 := hy

private theorem mul_lt_one_of_lt_of_le₀ {x y : Γ₀} (hx : x < 1) (hy : y ≤ 1) : x * y < 1 := by
  rw [mul_comm]
  exact mul_lt_one_of_le_of_lt₀ hy hx

end OrderAux

section Core

open NumberField

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {p : ℕ}

private theorem val_form_le_one (Φ : ∀ {R : Type _} [CommRing R], R → R)
    (hΦ : ∀ x : (v.valuation F).integer, ((Φ x : (v.valuation F).integer) : F) = Φ (x : F))
    {u : F} (hu : v.valuation F u ≤ 1) : v.valuation F (Φ u) ≤ 1 := by
  have h := (Φ (⟨u, hu⟩ : (v.valuation F).integer)).2
  rw [Valuation.mem_integer_iff, hΦ] at h
  exact h

private theorem val_form₂_le_one (Φ : ∀ {R : Type _} [CommRing R], R → R → R)
    (hΦ : ∀ x y : (v.valuation F).integer, ((Φ x y : (v.valuation F).integer) : F) = Φ (x : F) (y : F))
    {n d : F} (hn : v.valuation F n ≤ 1) (hd : v.valuation F d ≤ 1) : v.valuation F (Φ n d) ≤ 1 := by
  have h := (Φ (⟨n, hn⟩ : (v.valuation F).integer) ⟨d, hd⟩).2
  rw [Valuation.mem_integer_iff, hΦ] at h
  exact h

variable (hv : v.asIdeal.comap (algebraMap ℤ (𝓞 F)) = Ideal.span {(p : ℤ)}) (hp : p.Prime)
  (hp30 : ¬ p ∣ 30)
include hv hp hp30

private theorem val_natCast_eq_one {c : ℕ} (k : ℕ) (hc : c ∣ 30 ^ k) : v.valuation F (c : F) = 1 := by
  have h : ¬ (p : ℤ) ∣ (c : ℤ) := by
    intro h
    exact hp30 (hp.dvd_of_dvd_pow ((Int.natCast_dvd_natCast.mp h).trans hc))
  have := (Val.valuation_intCast_eq_one_iff v hv (c : ℤ)).mpr h
  simpa using this

variable {a b l : ℤ} (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) (hpD : ¬ (p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2)
  {u : F} (h₀ : IsKleinDatum (a : F) (b : F) u)
include hpa hpb hpD h₀

omit hpb in

theorem val_u_le_one : v.valuation F u ≤ 1 := by
  set w := v.valuation F with hw
  set D : F := 4 * (a : F) ^ 3 + 27 * (b : F) ^ 2 with hD
  have hwD : w D = 1 := by
    have := (Val.valuation_intCast_eq_one_iff v hv (4 * a ^ 3 + 27 * b ^ 2)).mpr hpD
    simpa [hD] using this
  have hwa : w (a : F) = 1 := (Val.valuation_intCast_eq_one_iff v hv a).mpr hpa
  set P : F[X] := C D * kleinH X ^ 3 + C (6912 * (a : F) ^ 3) * kleinV X ^ 5 with hP

  set S := Polynomial.liftsRing (w).integer.subtype with hS
  have hXS : (X : F[X]) ∈ S := by
    rw [hS, ← Val.coeff_le_one_iff_mem_lifts]
    intro i; rw [coeff_X]; split_ifs <;> simp
  have hCS : ∀ c : F, w c ≤ 1 → C c ∈ S := by
    intro c hc
    rw [hS, ← Val.coeff_le_one_iff_mem_lifts]
    intro i; rw [coeff_C]; split_ifs <;> simp [hc]
  have hHS : kleinH (X : F[X]) ∈ S := by
    have h := (kleinH (⟨X, hXS⟩ : S)).2
    rwa [show ((kleinH (⟨X, hXS⟩ : S) : S) : F[X]) = kleinH X from map_kleinH S.subtype _] at h
  have hVS : kleinV (X : F[X]) ∈ S := by
    have h := (kleinV (⟨X, hXS⟩ : S)).2
    rwa [show ((kleinV (⟨X, hXS⟩ : S) : S) : F[X]) = kleinV X from map_kleinV S.subtype _] at h
  have hPS : P ∈ S := by
    refine S.add_mem (S.mul_mem (hCS _ hwD.le) (S.pow_mem hHS 3)) (S.mul_mem (hCS _ ?_) (S.pow_mem hVS 5))
    rw [map_mul, map_pow, hwa, one_pow, mul_one]
    have h6912 : w (6912 : F) = 1 := by simpa using val_natCast_eq_one v hv hp hp30 (c := 6912) 8 (by norm_num)
    exact h6912.le
  have hcoeff : ∀ i, w (P.coeff i) ≤ 1 := (Val.coeff_le_one_iff_mem_lifts w P).mpr hPS

  have h60 : P.coeff 60 = D := by
    have h1 : (kleinH (X : F[X]) ^ 3).coeff 60 = 1 := by
      have := coeff_pow_of_natDegree_le (natDegree_kleinH_X_le (R := F)) (m := 3)
      rw [show 3 * 20 = 60 from rfl, coeff_kleinH_X, one_pow] at this
      exact this
    have h2 : (kleinV (X : F[X]) ^ 5).coeff 60 = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      calc (kleinV (X : F[X]) ^ 5).natDegree ≤ 5 * (kleinV (X : F[X])).natDegree := natDegree_pow_le
        _ ≤ 5 * 11 := Nat.mul_le_mul_left 5 natDegree_kleinV_X_le
        _ < 60 := by norm_num
    rw [hP, coeff_add, coeff_C_mul, coeff_C_mul, h1, h2, mul_one, mul_zero, add_zero]
  have hD0 : D ≠ 0 := by
    intro h; rw [h, map_zero] at hwD; exact zero_ne_one hwD
  have hdegle : P.natDegree ≤ 60 := by
    rw [hP]
    refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans ?_)
      ((natDegree_C_mul_le _ _).trans ?_)
    · exact natDegree_pow_le.trans (by linarith [natDegree_kleinH_X_le (R := F)])
    · exact natDegree_pow_le.trans (by linarith [natDegree_kleinV_X_le (R := F)])
  have hdeg : P.natDegree = 60 :=
    le_antisymm hdegle (le_natDegree_of_ne_zero (by rw [h60]; exact hD0))
  have hlead : w P.leadingCoeff = 1 := by
    rw [leadingCoeff, hdeg, h60, hwD]

  have hroot : P.IsRoot u := by
    rw [IsRoot.def, hP, eval_add, eval_mul, eval_mul, eval_C, eval_C, eval_pow, eval_pow,
      ← coe_evalRingHom, map_kleinH, map_kleinV, coe_evalRingHom, eval_X]
    linear_combination h₀.1
  exact Val.le_one_of_isRoot w hcoeff hlead hroot

theorem val_units :
    v.valuation F (kleinH u) = 1 ∧ v.valuation F (kleinV u) = 1 ∧ v.valuation F (kleinT u) = 1 ∧
      v.valuation F u = 1 ∧ v.valuation F (kleinF u) = 1 := by
  set w := v.valuation F with hw
  have hu := val_u_le_one v hv hp hp30 hpa hpD h₀
  have hwa : w (a : F) = 1 := (Val.valuation_intCast_eq_one_iff v hv a).mpr hpa
  have hwb : w (b : F) = 1 := (Val.valuation_intCast_eq_one_iff v hv b).mpr hpb
  have hwD : w (4 * (a : F) ^ 3 + 27 * (b : F) ^ 2) = 1 := by
    have := (Val.valuation_intCast_eq_one_iff v hv (4 * a ^ 3 + 27 * b ^ 2)).mpr hpD
    simpa using this
  have hH : w (kleinH u) ≤ 1 := val_form_le_one v kleinH (fun x ↦ map_kleinH (v.valuation F).integer.subtype x) hu
  have hV : w (kleinV u) ≤ 1 := val_form_le_one v kleinV (fun x ↦ map_kleinV (v.valuation F).integer.subtype x) hu
  have hT : w (kleinT u) ≤ 1 := val_form_le_one v kleinT (fun x ↦ map_kleinT (v.valuation F).integer.subtype x) hu
  have hFu : w (kleinF u) ≤ 1 := val_form_le_one v kleinF (fun x ↦ map_kleinF (v.valuation F).integer.subtype x) hu

  have h35 : w (kleinH u) ^ 3 = w (kleinV u) ^ 5 := by
    have heq : kleinH u ^ 3 * (4 * (a : F) ^ 3 + 27 * (b : F) ^ 2) = -(6912 * (a : F) ^ 3 * kleinV u ^ 5) :=
      eq_neg_of_add_eq_zero_left h₀.1
    have := congrArg w heq
    have h6912 : w (6912 : F) = 1 := by simpa using val_natCast_eq_one v hv hp hp30 (c := 6912) 8 (by norm_num)
    rw [map_mul, map_pow, hwD, mul_one, Valuation.map_neg, map_mul, map_mul, map_pow, map_pow, hwa, one_pow,
      mul_one, h6912, one_mul] at this
    exact this

  have hV1 : w (kleinV u) = 1 := by
    by_contra hne
    have hVlt : w (kleinV u) < 1 := lt_of_le_of_ne hV hne
    have hHlt : w (kleinH u) < 1 := by
      by_contra hH1
      have hH1 : w (kleinH u) = 1 := le_antisymm hH (not_lt.mp hH1)
      rw [hH1, one_pow] at h35
      exact (pow_lt_one₀ zero_le' hVlt (by norm_num)).ne h35.symm
    have hbez := congrArg w (bezout_HV u)
    have h3125 : w (3125 : F) = 1 := by simpa using val_natCast_eq_one v hv hp hp30 (c := 3125) 5 (by norm_num)
    rw [h3125] at hbez
    have hlt : w (bezHVa u * kleinH u + bezHVb u * kleinV u) < 1 := by
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact mul_lt_one_of_le_of_lt₀ (val_form_le_one v bezHVa (fun x ↦ map_bezHVa (v.valuation F).integer.subtype x) hu) hHlt
      · rw [map_mul]
        exact mul_lt_one_of_le_of_lt₀ (val_form_le_one v bezHVb (fun x ↦ map_bezHVb (v.valuation F).integer.subtype x) hu) hVlt
    exact hlt.ne hbez
  have hH1 : w (kleinH u) = 1 := by
    by_contra hne
    have := pow_lt_one₀ zero_le' (lt_of_le_of_ne hH hne) (n := 3) (by norm_num)
    rw [h35, hV1, one_pow] at this
    exact lt_irrefl _ this

  have hT1 : w (kleinT u) = 1 := by
    have heq := congrArg w h₀.kleinT_sq_mul
    have h46656 : w (46656 : F) = 1 := by
      simpa using val_natCast_eq_one v hv hp hp30 (c := 46656) 6 (by norm_num)
    rw [map_mul, map_pow, hwD, mul_one, map_mul, map_mul, map_pow, map_pow, hwb, hV1, one_pow, one_pow,
      mul_one, mul_one, h46656] at heq
    by_contra hne
    have := pow_lt_one₀ zero_le' (lt_of_le_of_ne hT hne) (n := 2) (by norm_num)
    rw [heq] at this
    exact lt_irrefl _ this

  have hsplit : w u * w (kleinF u) = 1 := by rw [← map_mul, ← kleinV_eq_mul_kleinF, hV1]
  have hu1 : w u = 1 := by
    by_contra hne
    exact (mul_lt_one_of_lt_of_le₀ (lt_of_le_of_ne hu hne) hFu).ne hsplit
  have hF1 : w (kleinF u) = 1 := by rwa [hu1, one_mul] at hsplit
  exact ⟨hH1, hV1, hT1, hu1, hF1⟩

theorem val_datum :
    v.valuation F (rsBeta u) ≤ 1 ∧ v.valuation F (rsGamma u) ≤ 1 ∧
      v.valuation F (rsBeta u - u * rsGamma u) = 1 := by
  set w := v.valuation F with hw
  have hu := val_u_le_one v hv hp hp30 hpa hpD h₀
  obtain ⟨hH1, -, hT1, hu1, hF1⟩ := val_units v hv hp hp30 hpa hpb hpD h₀
  have h144 : w (144 : F) = 1 := by
    have := val_natCast_eq_one v hv hp hp30 (c := 144) 4 (by norm_num); simpa using this
  have hden₁ : w (144 * u ^ 4 * kleinF u ^ 4) = 1 := by
    rw [map_mul, map_mul, map_pow, map_pow, h144, hu1, hF1, one_pow, one_mul, one_mul]
  have hden₂ : w (144 * kleinF u ^ 4) = 1 := by
    rw [map_mul, map_pow, h144, hF1, one_pow, one_mul]
  have hβ : w (rsBeta u) ≤ 1 := by
    rw [rsBeta_eq, map_div₀, hden₁, div_one, map_mul, hT1, one_mul]
    exact val_form_le_one v rsBetaNum (fun x ↦ map_rsBetaNum (v.valuation F).integer.subtype x) hu
  have hγ : w (rsGamma u) ≤ 1 := by
    rw [rsGamma_eq, map_div₀, hden₂, div_one, map_mul, hT1, one_mul]
    exact val_form_le_one v rsGammaNum (fun x ↦ map_rsGammaNum (v.valuation F).integer.subtype x) hu
  have hu0 : u ≠ 0 := by intro h; rw [h, map_zero] at hu1; exact zero_ne_one hu1
  have hF0 : kleinF u ≠ 0 := by intro h; rw [h, map_zero] at hF1; exact zero_ne_one hF1
  have hδ : w (rsBeta u - u * rsGamma u) = 1 := by
    rw [rsBeta_sub_mul_rsGamma u hu0 hF0, map_div₀, Valuation.map_neg, map_mul, hT1, hH1, hden₁, one_mul,
      div_one]
  exact ⟨hβ, hγ, hδ⟩

theorem val_coeff_poly_le_one :
    (∀ k, v.valuation F ((polyA (a : F) u (l : F)).coeff k) ≤ 1) ∧
      ∀ k, v.valuation F ((polyB (b : F) u (l : F)).coeff k) ≤ 1 := by
  set w := v.valuation F with hw
  have hu := val_u_le_one v hv hp hp30 hpa hpD h₀
  obtain ⟨hH1, -, hT1, -, -⟩ := val_units v hv hp hp30 hpa hpb hpD h₀
  obtain ⟨hβ, hγ, -⟩ := val_datum v hv hp hp30 hpa hpb hpD h₀
  have hwa : w (a : F) = 1 := (Val.valuation_intCast_eq_one_iff v hv a).mpr hpa
  have hwb : w (b : F) = 1 := (Val.valuation_intCast_eq_one_iff v hv b).mpr hpb
  have hwl : w (l : F) ≤ 1 := Val.valuation_intCast_le_one v l
  set S := Polynomial.liftsRing (w).integer.subtype with hS
  have hXS : (X : F[X]) ∈ S := by
    rw [hS, ← Val.coeff_le_one_iff_mem_lifts]
    intro i; rw [coeff_X]; split_ifs <;> simp
  have hCS : ∀ c : F, w c ≤ 1 → C c ∈ S := by
    intro c hc
    rw [hS, ← Val.coeff_le_one_iff_mem_lifts]
    intro i; rw [coeff_C]; split_ifs <;> simp [hc]
  have h1S : (1 : F[X]) ∈ S := S.one_mem

  have hnS : C (rsBeta u + (l : F) * u) * X + C u ∈ S := by
    refine S.add_mem (S.mul_mem (hCS _ ?_) hXS) (hCS _ hu)
    exact Valuation.map_add_le w hβ (by rw [map_mul]; exact mul_le_one' hwl hu)
  have hdS : C (rsGamma u + (l : F)) * X + 1 ∈ S :=
    S.add_mem (S.mul_mem (hCS _ (Valuation.map_add_le w hγ hwl)) hXS) h1S
  have hHS : kleinHHom (C (rsBeta u + (l : F) * u) * X + C u) (C (rsGamma u + (l : F)) * X + 1) ∈ S := by
    have h := (kleinHHom (⟨_, hnS⟩ : S) ⟨_, hdS⟩).2
    rwa [show ((kleinHHom (⟨_, hnS⟩ : S) ⟨_, hdS⟩ : S) : F[X]) = _ from map_kleinHHom S.subtype _ _] at h
  have hTS : kleinTHom (C (rsBeta u + (l : F) * u) * X + C u) (C (rsGamma u + (l : F)) * X + 1) ∈ S := by
    have h := (kleinTHom (⟨_, hnS⟩ : S) ⟨_, hdS⟩).2
    rwa [show ((kleinTHom (⟨_, hnS⟩ : S) ⟨_, hdS⟩ : S) : F[X]) = _ from map_kleinTHom S.subtype _ _] at h
  have hA : polyA (a : F) u (l : F) ∈ S := by
    refine S.mul_mem (hCS _ ?_) hHS
    rw [map_div₀, hwa, hH1, div_one]
  have hB : polyB (b : F) u (l : F) ∈ S := by
    refine S.mul_mem (hCS _ ?_) hTS
    rw [map_div₀, hwb, hT1, div_one]
  exact ⟨(Val.coeff_le_one_iff_mem_lifts w _).mpr hA, (Val.coeff_le_one_iff_mem_lifts w _).mpr hB⟩

theorem not_val_lt_one_and (t₀ : ℤ) :
    ¬ (v.valuation F (rsFamilyA (a : F) u (l : F) (t₀ : F)) < 1 ∧
        v.valuation F (rsFamilyB (b : F) u (l : F) (t₀ : F)) < 1) := by
  set w := v.valuation F with hw
  have hu := val_u_le_one v hv hp hp30 hpa hpD h₀
  obtain ⟨hH1, -, hT1, hu1, -⟩ := val_units v hv hp hp30 hpa hpb hpD h₀
  obtain ⟨hβ, hγ, hδ⟩ := val_datum v hv hp hp30 hpa hpb hpD h₀
  have hwa : w (a : F) = 1 := (Val.valuation_intCast_eq_one_iff v hv a).mpr hpa
  have hwb : w (b : F) = 1 := (Val.valuation_intCast_eq_one_iff v hv b).mpr hpb
  have hwl : w (l : F) ≤ 1 := Val.valuation_intCast_le_one v l
  have hwt : w (t₀ : F) ≤ 1 := Val.valuation_intCast_le_one v t₀
  set n₀ : F := rsNum u (l : F) (t₀ : F) with hn₀
  set d₀ : F := rsDen u (l : F) (t₀ : F) with hd₀
  have hc₁ : w (rsBeta u + (l : F) * u) ≤ 1 :=
    Valuation.map_add_le w hβ (by rw [map_mul]; exact mul_le_one' hwl hu)
  have hc₂ : w (rsGamma u + (l : F)) ≤ 1 := Valuation.map_add_le w hγ hwl
  have hn : w n₀ ≤ 1 := by
    rw [hn₀, rsNum]
    exact Valuation.map_add_le w (by rw [map_mul]; exact mul_le_one' hc₁ hwt) hu
  have hd : w d₀ ≤ 1 := by
    rw [hd₀, rsDen]
    exact Valuation.map_add_le w (by rw [map_mul]; exact mul_le_one' hc₂ hwt) (by rw [map_one])

  have hA : w (rsFamilyA (a : F) u (l : F) (t₀ : F)) = w (kleinHHom n₀ d₀) := by
    rw [rsFamilyA, map_div₀, map_mul, hwa, hH1, one_mul, div_one]
  have hB : w (rsFamilyB (b : F) u (l : F) (t₀ : F)) = w (kleinTHom n₀ d₀) := by
    rw [rsFamilyB, map_div₀, map_mul, hwb, hT1, one_mul, div_one]
  rw [hA, hB]
  rintro ⟨hHlt, hTlt⟩
  rcases hd.lt_or_eq with hdlt | hdeq
  ·
    have hn1 : w n₀ = 1 := by
      by_contra hne
      have hnlt : w n₀ < 1 := lt_of_le_of_ne hn hne
      have hdet : rsBeta u - u * rsGamma u = (rsBeta u + (l : F) * u) * d₀ - (rsGamma u + (l : F)) * n₀ := by
        rw [hn₀, hd₀, rsNum, rsDen]; ring
      have : w (rsBeta u - u * rsGamma u) < 1 := by
        rw [hdet]
        refine Valuation.map_sub_lt w ?_ ?_
        · rw [map_mul]; exact mul_lt_one_of_le_of_lt₀ hc₁ hdlt
        · rw [map_mul]; exact mul_lt_one_of_le_of_lt₀ hc₂ hnlt
      exact this.ne hδ
    have htail : w (d₀ * kleinHTail n₀ d₀) < 1 := by
      rw [map_mul]
      exact mul_lt_one_of_lt_of_le₀ hdlt (val_form₂_le_one v kleinHTail (fun x y ↦ map_kleinHTail (v.valuation F).integer.subtype x y) hn hd)
    have : w (kleinHHom n₀ d₀) = 1 := by
      rw [kleinHHom_eq_add_tail, Valuation.map_add_eq_of_lt_left w (by rwa [map_pow, hn1, one_pow]),
        map_pow, hn1, one_pow]
    exact hHlt.ne this
  ·
    have hd0 : d₀ ≠ 0 := by intro h; rw [h, map_zero] at hdeq; exact zero_ne_one hdeq
    set u₁ := n₀ / d₀ with hu₁
    have hu₁le : w u₁ ≤ 1 := by rw [hu₁, map_div₀, hdeq, div_one]; exact hn
    have hH' : w (kleinH u₁) < 1 := by
      rw [kleinHHom_eq_pow_mul n₀ d₀ hd0, map_mul, map_pow, hdeq, one_pow, one_mul] at hHlt
      exact hHlt
    have hT' : w (kleinT u₁) < 1 := by
      rw [kleinTHom_eq_pow_mul n₀ d₀ hd0, map_mul, map_pow, hdeq, one_pow, one_mul] at hTlt
      exact hTlt
    have hbez := congrArg w (bezout_HT u₁)
    have hbig : w (1406250000 : F) = 1 := by
      simpa using val_natCast_eq_one v hv hp hp30 (c := 1406250000) 10 (by norm_num)
    rw [hbig] at hbez
    have hlt : w (bezHTa u₁ * kleinH u₁ + bezHTb u₁ * kleinT u₁) < 1 := by
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact mul_lt_one_of_le_of_lt₀ (val_form_le_one v bezHTa (fun x ↦ map_bezHTa (v.valuation F).integer.subtype x) hu₁le) hH'
      · rw [map_mul]
        exact mul_lt_one_of_le_of_lt₀ (val_form_le_one v bezHTb (fun x ↦ map_bezHTb (v.valuation F).integer.subtype x) hu₁le) hT'
    exact hlt.ne hbez

end Core

section Heads

variable {K : Type*} [Field K] [CharZero K]

namespace IsKleinDatum

private theorem _root_.RubinSilverberg.IsKleinDatum.isIntegral {a b : ℤ} {u₀ : K} (h₀ : IsKleinDatum (a : K) (b : K) u₀)
    (hD : (4 * a ^ 3 + 27 * b ^ 2 : ℤ) ≠ 0) : IsIntegral ℚ u₀ := by
  set D : ℚ := 4 * (a : ℚ) ^ 3 + 27 * (b : ℚ) ^ 2 with hDdef
  have hD' : D ≠ 0 := by rw [hDdef]; exact_mod_cast hD
  set P : ℚ[X] := C D * kleinH X ^ 3 + C (6912 * (a : ℚ) ^ 3) * kleinV X ^ 5 with hP
  have h60 : P.coeff 60 = D := by
    have h1 : (kleinH (X : ℚ[X]) ^ 3).coeff 60 = 1 := by
      have := coeff_pow_of_natDegree_le (natDegree_kleinH_X_le (R := ℚ)) (m := 3)
      rw [show 3 * 20 = 60 from rfl, coeff_kleinH_X, one_pow] at this
      exact this
    have h2 : (kleinV (X : ℚ[X]) ^ 5).coeff 60 = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      calc (kleinV (X : ℚ[X]) ^ 5).natDegree ≤ 5 * (kleinV (X : ℚ[X])).natDegree := natDegree_pow_le
        _ ≤ 5 * 11 := Nat.mul_le_mul_left 5 natDegree_kleinV_X_le
        _ < 60 := by norm_num
    rw [hP, coeff_add, coeff_C_mul, coeff_C_mul, h1, h2, mul_one, mul_zero, add_zero]
  have hP0 : P ≠ 0 := by
    intro h; rw [h, coeff_zero] at h60; exact hD' h60.symm
  have heval : aeval u₀ P = 0 := by
    rw [hP, map_add, map_mul, map_mul, aeval_C, aeval_C, map_pow, map_pow, ← AlgHom.coe_toRingHom,
      map_kleinH, map_kleinV, AlgHom.coe_toRingHom, aeval_X]
    have := h₀.1
    simp only [hDdef, map_add, map_mul, map_pow, map_ofNat, eq_ratCast, Rat.cast_intCast]
    linear_combination this
  exact IsAlgebraic.isIntegral (K := ℚ) ⟨P, hP0, heval⟩

end IsKleinDatum
p2m_export "RubinSilverberg" "IsKleinDatum.isIntegral"

theorem not_dvd_den_coeff_gen {a b l : ℤ} {u₀ : K} (h₀ : IsKleinDatum (a : K) (b : K) u₀)
    {p : ℕ} (hp : p.Prime) (hp30 : ¬ p ∣ 30) (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b)
    (hpD : ¬ (p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2) {pa pb : ℚ[X]}
    (hpa' : ∀ t : K, rsFamilyA (a : K) u₀ (l : K) t = (pa.map (algebraMap ℚ K)).eval t)
    (hpb' : ∀ t : K, rsFamilyB (b : K) u₀ (l : K) t = (pb.map (algebraMap ℚ K)).eval t) :
    (∀ k, ¬ p ∣ (pa.coeff k).den) ∧ ∀ k, ¬ p ∣ (pb.coeff k).den := by
  have hD : (4 * a ^ 3 + 27 * b ^ 2 : ℤ) ≠ 0 := by rintro h; rw [h] at hpD; exact hpD (dvd_zero _)

  set F₀ := IntermediateField.adjoin ℚ {u₀} with hF₀
  haveI : FiniteDimensional ℚ F₀ := IntermediateField.adjoin.finiteDimensional (h₀.isIntegral hD)
  haveI : NumberField F₀ := ⟨⟩
  set u : F₀ := ⟨u₀, IntermediateField.mem_adjoin_simple_self ℚ u₀⟩ with hu
  have hcoe : (algebraMap F₀ K) u = u₀ := rfl
  have h₀' : IsKleinDatum (a : F₀) (b : F₀) u := by
    rw [← isKleinDatum_map_iff (algebraMap F₀ K)]
    simpa [hcoe] using h₀
  obtain ⟨v, hv⟩ := Val.exists_heightOneSpectrum_over (F := F₀) p hp
  haveI : Infinite K := Infinite.of_injective _ (Nat.cast_injective (R := K))

  have hidA : pa.map (Rat.castHom F₀) = polyA (a : F₀) u (l : F₀) := by
    apply Polynomial.map_injective (algebraMap F₀ K) (algebraMap F₀ K).injective
    rw [map_polyA, Polynomial.map_map]
    have h1 : pa.map ((algebraMap F₀ K).comp (Rat.castHom F₀)) = pa.map (algebraMap ℚ K) := by
      rw [Subsingleton.elim ((algebraMap F₀ K).comp (Rat.castHom F₀)) (algebraMap ℚ K)]
    rw [h1]
    apply Polynomial.funext
    intro t
    rw [← hpa' t, ← eval_polyA]
    simp [hcoe]
  have hidB : pb.map (Rat.castHom F₀) = polyB (b : F₀) u (l : F₀) := by
    apply Polynomial.map_injective (algebraMap F₀ K) (algebraMap F₀ K).injective
    rw [map_polyB, Polynomial.map_map]
    have h1 : pb.map ((algebraMap F₀ K).comp (Rat.castHom F₀)) = pb.map (algebraMap ℚ K) := by
      rw [Subsingleton.elim ((algebraMap F₀ K).comp (Rat.castHom F₀)) (algebraMap ℚ K)]
    rw [h1]
    apply Polynomial.funext
    intro t
    rw [← hpb' t, ← eval_polyB]
    simp [hcoe]
  obtain ⟨hcA, hcB⟩ := val_coeff_poly_le_one v hv hp hp30 hpa hpb hpD h₀' (l := l)
  constructor
  · intro k
    apply Val.not_dvd_den_of_valuation_le_one v hv hp
    have := hcA k
    rwa [← hidA, coeff_map, Rat.coe_castHom] at this
  · intro k
    apply Val.not_dvd_den_of_valuation_le_one v hv hp
    have := hcB k
    rwa [← hidB, coeff_map, Rat.coe_castHom] at this

theorem not_dvd_num_eval_and_gen {a b l : ℤ} {u₀ : K} (h₀ : IsKleinDatum (a : K) (b : K) u₀)
    {p : ℕ} (hp : p.Prime) (hp30 : ¬ p ∣ 30) (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b)
    (hpD : ¬ (p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2) {pa pb : ℚ[X]}
    (hpa' : ∀ t : K, rsFamilyA (a : K) u₀ (l : K) t = (pa.map (algebraMap ℚ K)).eval t)
    (hpb' : ∀ t : K, rsFamilyB (b : K) u₀ (l : K) t = (pb.map (algebraMap ℚ K)).eval t) (t₀ : ℤ) :
    ¬ ((p : ℤ) ∣ (pa.eval (t₀ : ℚ)).num ∧ (p : ℤ) ∣ (pb.eval (t₀ : ℚ)).num) := by
  have hD : (4 * a ^ 3 + 27 * b ^ 2 : ℤ) ≠ 0 := by rintro h; rw [h] at hpD; exact hpD (dvd_zero _)
  set F₀ := IntermediateField.adjoin ℚ {u₀} with hF₀
  haveI : FiniteDimensional ℚ F₀ := IntermediateField.adjoin.finiteDimensional (h₀.isIntegral hD)
  haveI : NumberField F₀ := ⟨⟩
  set u : F₀ := ⟨u₀, IntermediateField.mem_adjoin_simple_self ℚ u₀⟩ with hu
  have hcoe : (algebraMap F₀ K) u = u₀ := rfl
  have h₀' : IsKleinDatum (a : F₀) (b : F₀) u := by
    rw [← isKleinDatum_map_iff (algebraMap F₀ K)]
    simpa [hcoe] using h₀
  obtain ⟨v, hv⟩ := Val.exists_heightOneSpectrum_over (F := F₀) p hp
  haveI : Infinite K := Infinite.of_injective _ (Nat.cast_injective (R := K))
  have hidA : pa.map (Rat.castHom F₀) = polyA (a : F₀) u (l : F₀) := by
    apply Polynomial.map_injective (algebraMap F₀ K) (algebraMap F₀ K).injective
    rw [map_polyA, Polynomial.map_map]
    have h1 : pa.map ((algebraMap F₀ K).comp (Rat.castHom F₀)) = pa.map (algebraMap ℚ K) := by
      rw [Subsingleton.elim ((algebraMap F₀ K).comp (Rat.castHom F₀)) (algebraMap ℚ K)]
    rw [h1]
    apply Polynomial.funext
    intro t
    rw [← hpa' t, ← eval_polyA]
    simp [hcoe]
  have hidB : pb.map (Rat.castHom F₀) = polyB (b : F₀) u (l : F₀) := by
    apply Polynomial.map_injective (algebraMap F₀ K) (algebraMap F₀ K).injective
    rw [map_polyB, Polynomial.map_map]
    have h1 : pb.map ((algebraMap F₀ K).comp (Rat.castHom F₀)) = pb.map (algebraMap ℚ K) := by
      rw [Subsingleton.elim ((algebraMap F₀ K).comp (Rat.castHom F₀)) (algebraMap ℚ K)]
    rw [h1]
    apply Polynomial.funext
    intro t
    rw [← hpb' t, ← eval_polyB]
    simp [hcoe]

  have hvalA : ((pa.eval (t₀ : ℚ) : ℚ) : F₀) = rsFamilyA (a : F₀) u (l : F₀) (t₀ : F₀) := by
    rw [← eval_polyA, ← hidA, eval_map, ← Rat.coe_castHom, ← Polynomial.eval₂_at_apply]
    simp
  have hvalB : ((pb.eval (t₀ : ℚ) : ℚ) : F₀) = rsFamilyB (b : F₀) u (l : F₀) (t₀ : F₀) := by
    rw [← eval_polyB, ← hidB, eval_map, ← Rat.coe_castHom, ← Polynomial.eval₂_at_apply]
    simp

  obtain ⟨hcA, hcB⟩ := val_coeff_poly_le_one v hv hp hp30 hpa hpb hpD h₀' (l := l)
  have hwt : v.valuation F₀ (t₀ : F₀) ≤ 1 := Val.valuation_intCast_le_one v t₀
  have hintA : v.valuation F₀ ((pa.eval (t₀ : ℚ) : ℚ) : F₀) ≤ 1 := by
    rw [hvalA, ← eval_polyA, eval_eq_sum_range]
    refine Valuation.map_sum_le _ fun i _ ↦ ?_
    rw [map_mul, map_pow]
    exact mul_le_one' (hcA i) (pow_le_one₀ zero_le' hwt)
  have hintB : v.valuation F₀ ((pb.eval (t₀ : ℚ) : ℚ) : F₀) ≤ 1 := by
    rw [hvalB, ← eval_polyB, eval_eq_sum_range]
    refine Valuation.map_sum_le _ fun i _ ↦ ?_
    rw [map_mul, map_pow]
    exact mul_le_one' (hcB i) (pow_le_one₀ zero_le' hwt)
  have hdenA := Val.not_dvd_den_of_valuation_le_one v hv hp hintA
  have hdenB := Val.not_dvd_den_of_valuation_le_one v hv hp hintB
  rw [← Val.valuation_lt_one_iff_dvd_num v hv hdenA, ← Val.valuation_lt_one_iff_dvd_num v hv hdenB,
    hvalA, hvalB]
  exact not_val_lt_one_and v hv hp hp30 hpa hpb hpD h₀' t₀

end Heads

end RubinSilverberg

namespace RubinSilverberg
p2m_export "RubinSilverberg" "kleinV kleinH kleinT kleinHHom kleinTHom rsBeta rsGamma rsNum rsDen rsFamilyA rsFamilyB IsKleinDatum"
p2m_open "RubinSilverberg"

open Polynomial

theorem not_dvd_den_coeff_algClosure {a b l : ℤ} {u₀ : AlgebraicClosure ℚ}
    (h₀ : IsKleinDatum (algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)) (algebraMap ℚ (AlgebraicClosure ℚ) (b : ℚ)) u₀)
    {p : ℕ} (hp : p.Prime) (hp30 : ¬ p ∣ 30) (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b)
    (hpD : ¬ (p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2) {pa pb : Polynomial ℚ}
    (hpa' : ∀ t : AlgebraicClosure ℚ, rsFamilyA (algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)) u₀
      (algebraMap ℚ (AlgebraicClosure ℚ) (l : ℚ)) t = (pa.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t)
    (hpb' : ∀ t : AlgebraicClosure ℚ, rsFamilyB (algebraMap ℚ (AlgebraicClosure ℚ) (b : ℚ)) u₀
      (algebraMap ℚ (AlgebraicClosure ℚ) (l : ℚ)) t = (pb.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t) :
    (∀ k, ¬ p ∣ (pa.coeff k).den) ∧ ∀ k, ¬ p ∣ (pb.coeff k).den := by
  simp only [eq_ratCast, Rat.cast_intCast] at h₀ hpa' hpb'
  exact not_dvd_den_coeff_gen h₀ hp hp30 hpa hpb hpD hpa' hpb'

theorem not_dvd_num_eval_and_algClosure {a b l : ℤ} {u₀ : AlgebraicClosure ℚ}
    (h₀ : IsKleinDatum (algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)) (algebraMap ℚ (AlgebraicClosure ℚ) (b : ℚ)) u₀)
    {p : ℕ} (hp : p.Prime) (hp30 : ¬ p ∣ 30) (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b)
    (hpD : ¬ (p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2) {pa pb : Polynomial ℚ}
    (hpa' : ∀ t : AlgebraicClosure ℚ, rsFamilyA (algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)) u₀
      (algebraMap ℚ (AlgebraicClosure ℚ) (l : ℚ)) t = (pa.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t)
    (hpb' : ∀ t : AlgebraicClosure ℚ, rsFamilyB (algebraMap ℚ (AlgebraicClosure ℚ) (b : ℚ)) u₀
      (algebraMap ℚ (AlgebraicClosure ℚ) (l : ℚ)) t = (pb.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t)
    (t₀ : ℤ) :
    ¬ ((p : ℤ) ∣ (pa.eval (t₀ : ℚ)).num ∧ (p : ℤ) ∣ (pb.eval (t₀ : ℚ)).num) := by
  simp only [eq_ratCast, Rat.cast_intCast] at h₀ hpa' hpb'
  exact not_dvd_num_eval_and_gen h₀ hp hp30 hpa hpb hpD hpa' hpb' t₀

end RubinSilverberg

p2m_open "RubinSilverberg P2MW.S_RubinSilverberg_not_dvd_num_eval_and.RubinSilverberg"

theorem solution {a b l : ℤ} {u₀ : AlgebraicClosure ℚ} (h₀ : IsKleinDatum (algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)) (algebraMap ℚ (AlgebraicClosure ℚ) (b : ℚ)) u₀) {p : ℕ} (hp : p.Prime) (hp30 : ¬ p ∣ 30) (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) (hpD : ¬ (p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2) {pa pb : Polynomial ℚ} (hpa' : ∀ t : AlgebraicClosure ℚ, rsFamilyA (algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) (l : ℚ)) t = (pa.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t) (hpb' : ∀ t : AlgebraicClosure ℚ, rsFamilyB (algebraMap ℚ (AlgebraicClosure ℚ) (b : ℚ)) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) (l : ℚ)) t = (pb.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t) (t₀ : ℤ) : ¬ ((p : ℤ) ∣ (pa.eval (t₀ : ℚ)).num ∧ (p : ℤ) ∣ (pb.eval (t₀ : ℚ)).num) :=
  RubinSilverberg.not_dvd_num_eval_and_algClosure h₀ hp hp30 hpa hpb hpD hpa' hpb' t₀

end S_RubinSilverberg_not_dvd_num_eval_and
end P2MW
export P2MW.S_RubinSilverberg_not_dvd_num_eval_and (solution)
