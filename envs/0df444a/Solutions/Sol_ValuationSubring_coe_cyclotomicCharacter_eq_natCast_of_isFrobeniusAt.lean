-- Prove2me | solution 1 for ValuationSubring.coe_cyclotomicCharacter_eq_natCast_of_isFrobeniusAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/41a388e7-140a-54bf-93fb-6777318d3a3d

import Mathlib
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_coe_cyclotomicCharacter_eq_natCast_of_isFrobeniusAt

set_option autoImplicit false

open IsLocalRing

namespace CycloFrob

variable {L : Type*} [Field L]

theorem mem_of_pow_eq_one (A : ValuationSubring L) {t : L} {N : ℕ} (hN : 0 < N) (ht : t ^ N = 1) :
    t ∈ A := by
  rcases A.mem_or_inv_mem t with h | h
  · exact h
  · have h1 : t ^ (N - 1) * t = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hN, ht]
    rw [eq_inv_of_mul_eq_one_right h1, ← inv_pow]
    exact pow_mem h _

theorem geom_sum_eq_zero_of_pow_eq_one {R : Type*} [CommRing R] [IsDomain R] {w : R} {N : ℕ}
    (hw : w ^ N = 1) (hw1 : w ≠ 1) : (Finset.range N).sum (fun i => w ^ i) = 0 := by
  have h := mul_geom_sum w N
  rw [hw, sub_self] at h

  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hw1
  · exact h1

theorem one_sub_dvd_natCast_of_pow_eq_one {R : Type*} [CommRing R] [IsDomain R] {w : R} {N : ℕ}
    (hw : w ^ N = 1) (hw1 : w ≠ 1) : (1 - w) ∣ (N : R) := by
  have hsum : (N : R) = (Finset.range N).sum (fun i => (1 - w ^ i)) := by
    rw [Finset.sum_sub_distrib, geom_sum_eq_zero_of_pow_eq_one hw hw1, sub_zero, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
  rw [hsum]
  exact Finset.dvd_sum fun i _ => by
    have := sub_dvd_pow_sub_pow (1 : R) w i
    rwa [one_pow] at this

theorem eq_of_pow_eq_one_of_sub_mem (A : ValuationSubring L) {N : ℕ} (hN : 0 < N)
    (hNunit : IsUnit ((N : ℕ) : A)) {x y : A} (hx : x ^ N = 1) (hy : y ^ N = 1)
    (hxy : x - y ∈ maximalIdeal A) : x = y := by
  by_contra hne

  have hxinv : x ^ (N - 1) * x = 1 := by rw [← pow_succ, Nat.sub_add_cancel hN, hx]
  set w : A := x ^ (N - 1) * y with hw
  have hwN : w ^ N = 1 := by
    rw [hw, mul_pow, ← pow_mul, mul_comm (N - 1) N, pow_mul, hx, one_pow, one_mul, hy]
  have hw1 : w ≠ 1 := by
    intro h1
    apply hne
    have : x * w = y := by
      rw [hw, ← mul_assoc, mul_comm x, hxinv, one_mul]
    rw [← this, h1, mul_one]
  have hdvd : (1 - w) ∣ ((N : ℕ) : A) := one_sub_dvd_natCast_of_pow_eq_one hwN hw1
  have hunit : IsUnit (1 - w) := isUnit_of_dvd_unit hdvd hNunit

  have hmem : 1 - w ∈ maximalIdeal A := by
    have : 1 - w = x ^ (N - 1) * (x - y) := by
      rw [mul_sub, hxinv, hw]
    rw [this]
    exact Ideal.mul_mem_left _ _ hxy
  exact (mem_maximalIdeal _ |>.mp hmem) hunit

end CycloFrob

open CycloFrob in
theorem solution
    {p : ℕ} [Fact p.Prime] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = ℓ := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨hσd, hσres⟩ := hσ
  set d : A.decompositionSubgroup ℚ := ⟨σ, hσd⟩ with hd

  have hℓmem : ((ℓ : ℕ) : A) ∈ maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    exact hA
  have hpunit : IsUnit ((p : ℕ) : A) := by
    by_contra hpu
    have hpmem : ((p : ℕ) : A) ∈ maximalIdeal A := (mem_maximalIdeal _).mpr hpu
    have hcop : IsCoprime ((p : ℕ) : A) ((ℓ : ℕ) : A) :=
      Nat.Coprime.cast ((Nat.coprime_primes hp hℓ).mpr (Ne.symm hℓp))
    obtain ⟨u, v, huv⟩ := hcop
    apply (maximalIdeal.isMaximal A).ne_top
    rw [Ideal.eq_top_iff_one, ← huv]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpmem) (Ideal.mul_mem_left _ _ hℓmem)

  have key : ∀ (n : ℕ) (t : AlgebraicClosure ℚ), t ^ (p ^ n) = 1 → σ t = t ^ ℓ := by
    intro n t htN
    have hNpos : 0 < p ^ n := pow_pos hp.pos n
    have hNunit : IsUnit (((p ^ n : ℕ) : ℕ) : A) := by
      rw [Nat.cast_pow]
      exact hpunit.pow n
    have htA : t ∈ A := mem_of_pow_eq_one A hNpos htN
    set a : A := ⟨t, htA⟩ with ha
    have haN : a ^ (p ^ n) = 1 := Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact htN)

    have hσa_coe : ((d • a : A) : AlgebraicClosure ℚ) = σ t := rfl
    have hσaN : (d • a) ^ (p ^ n) = 1 := by rw [← smul_pow', haN, smul_one]
    have haℓN : (a ^ ℓ) ^ (p ^ n) = 1 := by rw [← pow_mul, mul_comm, pow_mul, haN, one_pow]

    have hres : residue A (d • a) = residue A (a ^ ℓ) := by
      rw [ResidueField.residue_smul, hσres, map_pow]
    have hsub : d • a - a ^ ℓ ∈ maximalIdeal A := Ideal.Quotient.eq.mp hres
    have heq : d • a = a ^ ℓ := eq_of_pow_eq_one_of_sub_mem A hNpos hNunit hσaN haℓN hsub
    have := congrArg (fun x : A => (x : AlgebraicClosure ℚ)) heq
    simpa only [hσa_coe, SubmonoidClass.coe_pow] using this

  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [cyclotomicCharacter.toZModPow p σ.toRingEquiv (n := n), map_natCast]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have htN : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (p ^ n) = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ t).mp ht, Units.val_one]
  have hmod : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (ℓ : ZMod (p ^ n)).val =
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ ℓ := by
    rw [ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div ℓ (p ^ n), pow_add, pow_mul, htN, one_pow, mul_one]
  rw [hmod]
  exact key n _ htN

end S_ValuationSubring_coe_cyclotomicCharacter_eq_natCast_of_isFrobeniusAt
end P2MW
export P2MW.S_ValuationSubring_coe_cyclotomicCharacter_eq_natCast_of_isFrobeniusAt (solution)
