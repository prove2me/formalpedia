-- Prove2me | solution 1 for ValuationSubring.tameCharacter_pow_succ_eq_natCast_of_pow_eq_of_mem_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5dcd2899-b200-5516-b106-5bfc36016543

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_tameCharacter_eq_of_div_mem_of_div_mem
import Theorems.Thm_ValuationSubring_tameCharacter_sub_one_eq_natCast
import Theorems.Thm_ValuationSubring_tameCharacter_pow_left
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_tameCharacter_pow_succ_eq_natCast_of_pow_eq_of_mem_inertiaSubgroupIn
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

namespace TameNormOfLevelTwo

private theorem mem_of_pow_eq_one (P : ValuationSubring (AlgebraicClosure ℚ))
    {ζ : AlgebraicClosure ℚ} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) : ζ ∈ P := by
  refine P.mem_of_valuation_le_one ζ ?_
  by_contra h
  have h1 : (1 : _) < P.valuation ζ := not_le.mp h
  have h2 : P.valuation ζ ^ n = 1 := by rw [← map_pow, hζ, map_one]
  exact (ne_of_gt (one_lt_pow₀ h1 hn)) h2

private theorem isPrimitiveRoot_mk (P : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ)
    [hp : Fact p.Prime] {ζ : AlgebraicClosure ℚ} (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1) (hζP : ζ ∈ P) :
    IsPrimitiveRoot (⟨ζ, hζP⟩ : P) p := by
  have hzp : (⟨ζ, hζP⟩ : P) ^ p = 1 := Subtype.ext (by simpa using hζp)
  refine ⟨hzp, fun l hl => ?_⟩
  have hgcd : (⟨ζ, hζP⟩ : P) ^ Nat.gcd p l = 1 := pow_gcd_eq_one.mpr ⟨hzp, hl⟩
  rcases (Nat.dvd_prime hp.out).mp (Nat.gcd_dvd_left p l) with h1 | hpl
  · exfalso
    rw [h1, pow_one] at hgcd
    exact hζ1 (by simpa using congrArg Subtype.val hgcd)
  · rw [← hpl]
    exact Nat.gcd_dvd_right p l

private theorem exists_mul_eq_one_and_natCast_eq (P : ValuationSubring (AlgebraicClosure ℚ))
    (p : ℕ) [hp : Fact p.Prime] {ζ : AlgebraicClosure ℚ} (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (hζP : ζ ∈ P) :
    ∃ w w' : P, w * w' = 1 ∧ ((p : ℕ) : P) = w * ((⟨ζ, hζP⟩ : P) - 1) ^ (p - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero
  have hprim : IsPrimitiveRoot (⟨ζ, hζP⟩ : P) (m + 1) := by
    rw [← hm]; exact isPrimitiveRoot_mk P p hζp hζ1 hζP
  have hprod := hprim.prod_pow_sub_one_eq_order
  have hm' : Nat.Prime (m + 1) := by rw [← hm]; exact hp.out
  have hassoc : ∀ k : ℕ, k < m →
      ∃ v : Pˣ, ((⟨ζ, hζP⟩ : P) - 1) * (v : P) = (⟨ζ, hζP⟩ : P) ^ (k + 1) - 1 := fun k hk =>
    hprim.associated_sub_one_pow_sub_one_of_coprime
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hm').mpr
        (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos k) (by omega))))
  classical
  choose! u hu using hassoc
  have hfac : ∀ k ∈ Finset.range m,
      (⟨ζ, hζP⟩ : P) ^ (k + 1) - 1 = ((⟨ζ, hζP⟩ : P) - 1) * (u k : P) := fun k hk =>
    (hu k (Finset.mem_range.mp hk)).symm
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    at hprod
  refine ⟨(-1) ^ m * ∏ k ∈ Finset.range m, (u k : P),
    (-1) ^ m * ∏ k ∈ Finset.range m, (((u k)⁻¹ : Pˣ) : P), ?_, ?_⟩
  · have hunits : ∏ k ∈ Finset.range m, ((u k : P) * (((u k)⁻¹ : Pˣ) : P)) = 1 :=
      Finset.prod_eq_one fun k _ => Units.mul_inv (u k)
    rw [Finset.prod_mul_distrib] at hunits
    calc (-1 : P) ^ m * (∏ k ∈ Finset.range m, (u k : P)) *
          ((-1) ^ m * ∏ k ∈ Finset.range m, (((u k)⁻¹ : Pˣ) : P))
        = ((-1) ^ m * (-1) ^ m) *
            ((∏ k ∈ Finset.range m, (u k : P)) * ∏ k ∈ Finset.range m, (((u k)⁻¹ : Pˣ) : P)) := by
          ring
      _ = 1 := by
          rw [hunits, mul_one, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  · have hm1 : p - 1 = m := by omega
    rw [hm1, hm, Nat.cast_succ, ← hprod]
    ring

private theorem residue_mk_eq_one (P : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ)
    [Fact p.Prime] (hP : P.LiesOverPrime p) {ζ : AlgebraicClosure ℚ} (hζp : ζ ^ p = 1)
    (hζ1 : ζ ≠ 1) (hζP : ζ ∈ P) : IsLocalRing.residue P ⟨ζ, hζP⟩ = 1 := by
  obtain ⟨w, w', hww', hpw⟩ := exists_mul_eq_one_and_natCast_eq P p hζp hζ1 hζP
  have hpmem : ((p : ℕ) : P) ∈ IsLocalRing.maximalIdeal P := by
    exact (ValuationSubring.coe_mem_nonunits_iff (A := P)).mp hP
  have hwu : IsUnit w := ⟨⟨w, w', hww', by rw [mul_comm]; exact hww'⟩, rfl⟩
  rw [hpw, Ideal.unit_mul_mem_iff_mem (I := IsLocalRing.maximalIdeal P) hwu] at hpmem
  have hsub : (⟨ζ, hζP⟩ : P) - 1 ∈ IsLocalRing.maximalIdeal P :=
    (IsLocalRing.maximalIdeal.isMaximal P).isPrime.mem_of_pow_mem _ hpmem
  have h0 := (IsLocalRing.residue_eq_zero_iff (R := P) _).mpr hsub
  rwa [map_sub, map_one, sub_eq_zero] at h0

private theorem div_mem_and_div_mem (P : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ)
    [hp : Fact p.Prime] {π : AlgebraicClosure ℚ} (hπ : π ^ (p - 1) = (p : AlgebraicClosure ℚ))
    {ζ : AlgebraicClosure ℚ} (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1) (hζP : ζ ∈ P) :
    (ζ - 1) / π ∈ P ∧ π / (ζ - 1) ∈ P := by
  obtain ⟨w, w', hww', hpw⟩ := exists_mul_eq_one_and_natCast_eq P p hζp hζ1 hζP
  have hp1 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.out.one_lt
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hp1] at hπ
    exact hp.out.ne_zero (Nat.cast_eq_zero.mp hπ.symm)
  have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
  have hpw' : (p : AlgebraicClosure ℚ) = (w : AlgebraicClosure ℚ) * (ζ - 1) ^ (p - 1) := by
    have h1 := congrArg (fun t : P => (t : AlgebraicClosure ℚ)) hpw
    simpa using h1
  have hww'' : (w : AlgebraicClosure ℚ) * (w' : AlgebraicClosure ℚ) = 1 := by
    have h1 := congrArg (fun t : P => (t : AlgebraicClosure ℚ)) hww'
    simpa using h1
  have hw0 : (w : AlgebraicClosure ℚ) ≠ 0 := left_ne_zero_of_mul_eq_one hww''
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = m + 1 := Nat.exists_eq_succ_of_ne_zero hp1
  set x : AlgebraicClosure ℚ := (ζ - 1) / π with hx
  have hxpow : x ^ (m + 1) * (w : AlgebraicClosure ℚ) = 1 := by
    have hpow0 : (ζ - 1) ^ (p - 1) ≠ 0 := pow_ne_zero _ hζ1'
    rw [← hm, hx, div_pow, hπ, hpw']
    field_simp
  have hxinv : x⁻¹ = x ^ m * (w : AlgebraicClosure ℚ) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← hxpow]; ring
  have hw : x⁻¹ ^ (m + 1) = (w : AlgebraicClosure ℚ) := by
    rw [inv_pow]
    exact (eq_inv_of_mul_eq_one_right hxpow).symm
  have hxeq : x = x⁻¹ ^ m * (w' : AlgebraicClosure ℚ) := by
    have h3 : x⁻¹ * (x⁻¹ ^ m * (w' : AlgebraicClosure ℚ)) = 1 := by
      rw [← mul_assoc, ← pow_succ', hw, hww'']
    have h4 := inv_eq_of_mul_eq_one_right h3
    rwa [inv_inv] at h4
  have hdiv : π / (ζ - 1) = x⁻¹ := by rw [hx, inv_div]
  rcases P.mem_or_inv_mem x with hxP | hxP
  · refine ⟨hxP, ?_⟩
    rw [hdiv, hxinv]
    exact MulMemClass.mul_mem (pow_mem hxP m) w.2
  · refine ⟨?_, ?_⟩
    · rw [hxeq]
      exact MulMemClass.mul_mem (pow_mem hxP m) w'.2
    · rw [hdiv]; exact hxP

private theorem tameCharacter_eq_natCast_of_pow_pred_eq_of_mem_inertiaSubgroupIn
    (P : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [hp : Fact p.Prime]
    (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p - 1) = (p : AlgebraicClosure ℚ))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ)
    {ζ : AlgebraicClosure ℚ} (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1) {a : ℕ} (hσζ : σ ζ = ζ ^ a) :
    P.tameCharacter π σ = (a : IsLocalRing.ResidueField P) := by
  have hζP : ζ ∈ P := mem_of_pow_eq_one P hp.out.ne_zero hζp
  obtain ⟨hu', hu⟩ := div_mem_and_div_mem P p hπ hζp hζ1 hζP
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.sub_ne_zero_of_lt hp.out.one_lt)] at hπ
    exact hp.out.ne_zero (Nat.cast_eq_zero.mp hπ.symm)
  rw [P.tameCharacter_eq_of_div_mem_of_div_mem (ζ - 1) π (sub_ne_zero.mpr hζ1) hπ0 hu hu' hσ]
  exact P.tameCharacter_sub_one_eq_natCast hζP (residue_mk_eq_one P p hP hζp hζ1 hζP) hζ1 hσζ

end TameNormOfLevelTwo

theorem solution
    (P : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [Fact p.Prime] (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = (p : AlgebraicClosure ℚ))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ)
    {ζ : AlgebraicClosure ℚ} (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1) {a : ℕ} (hσζ : σ ζ = ζ ^ a) :
    P.tameCharacter π σ ^ (p + 1) = (a : IsLocalRing.ResidueField P) := by
  have hexp : (p + 1) * (p - 1) = p ^ 2 - 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := Nat.exists_eq_succ_of_ne_zero (Fact.out : p.Prime).ne_zero
    have h1 : (m + 1) ^ 2 = (m * m + 2 * m) + 1 := by ring
    rw [h1, Nat.add_sub_cancel, Nat.add_sub_cancel]
    ring
  have hπ' : (π ^ (p + 1)) ^ (p - 1) = (p : AlgebraicClosure ℚ) := by
    rw [← pow_mul, hexp, hπ]
  rw [← P.tameCharacter_pow_left π σ (p + 1)]
  exact TameNormOfLevelTwo.tameCharacter_eq_natCast_of_pow_pred_eq_of_mem_inertiaSubgroupIn P p hP (π ^ (p + 1)) hπ'
    hσ hζp hζ1 hσζ

end S_ValuationSubring_tameCharacter_pow_succ_eq_natCast_of_pow_eq_of_mem_inertiaSubgroupIn
end P2MW
export P2MW.S_ValuationSubring_tameCharacter_pow_succ_eq_natCast_of_pow_eq_of_mem_inertiaSubgroupIn (solution)
