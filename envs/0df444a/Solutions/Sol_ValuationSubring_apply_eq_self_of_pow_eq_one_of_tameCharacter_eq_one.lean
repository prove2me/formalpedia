-- Prove2me | solution 1 for ValuationSubring.apply_eq_self_of_pow_eq_one_of_tameCharacter_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b1cd306d-75dc-5bbd-8156-91eeb16b345f

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq
import Theorems.Thm_ValuationSubring_exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_tameCharacter_sub_one_eq_natCast
import Theorems.Thm_ValuationSubring_residue_eq_one_of_pow_prime_pow_eq_one
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_apply_eq_self_of_pow_eq_one_of_tameCharacter_eq_one
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open Polynomial

namespace InertZeta

open ValuationSubring

variable (P : ValuationSubring (AlgebraicClosure ℚ))

private theorem mem_of_pow_eq_one {u : AlgebraicClosure ℚ} {m : ℕ} (hm : 0 < m) (hu : u ^ m = 1) : u ∈ P := by
  rcases P.mem_or_inv_mem u with h | h
  · exact h
  · have key : u = (u ^ (m - 1))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ', Nat.sub_add_cancel hm, hu]
    rw [key, ← inv_pow]
    exact pow_mem h _

private theorem charP_residueField {p : ℕ} (hp : p.Prime) (hP : P.LiesOverPrime p) :
    CharP (IsLocalRing.ResidueField P) p := by
  have hP' : ((p : ℕ) : AlgebraicClosure ℚ) ∈ P.nonunits := hP
  have hpP : ((p : ℕ) : P) ∈ IsLocalRing.maximalIdeal P := by
    rw [← coe_mem_nonunits_iff, SubringClass.coe_natCast]
    exact hP'
  rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (IsLocalRing.residue P), IsLocalRing.residue_eq_zero_iff]
  exact hpP

private theorem valuation_geom_sum_eq_one {ζ : AlgebraicClosure ℚ} (hζP : ζ ∈ P)
    (hres : IsLocalRing.residue P ⟨ζ, hζP⟩ = 1) {j : ℕ} (hj : (j : IsLocalRing.ResidueField P) ≠ 0) :
    P.valuation (∑ i ∈ Finset.range j, ζ ^ i) = 1 := by
  have hsP : (∑ i ∈ Finset.range j, ζ ^ i) ∈ P := sum_mem (fun i _ => pow_mem hζP i)
  have hcoe : (⟨∑ i ∈ Finset.range j, ζ ^ i, hsP⟩ : P) = ∑ i ∈ Finset.range j, (⟨ζ, hζP⟩ : P) ^ i :=
    Subtype.ext (by
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [SubmonoidClass.coe_pow])
  have hres' : IsLocalRing.residue P ⟨_, hsP⟩ = j := by
    rw [hcoe, map_sum]
    simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hunit : IsUnit (⟨_, hsP⟩ : P) := by
    by_contra h
    have hmem : (⟨_, hsP⟩ : P) ∈ IsLocalRing.maximalIdeal P :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
    have h0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [hres'] at h0
    exact hj h0
  exact (P.valuation_eq_one_iff _).mp hunit

private theorem valuation_one_sub_pow (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q) {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ q) :
    P.valuation (1 - ζ) ^ (q - 1) = P.valuation (q : AlgebraicClosure ℚ) := by
  have hq : q.Prime := Fact.out
  haveI := charP_residueField P hq hP
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hζP : ζ ∈ P := mem_of_pow_eq_one P hq.pos hζ.pow_eq_one
  have hres : IsLocalRing.residue P ⟨ζ, hζP⟩ = 1 :=
    ValuationSubring.residue_eq_one_of_pow_prime_pow_eq_one P hq hP (n := 1) (by rw [pow_one]; exact hζ.pow_eq_one) hζP
  have hprod : (q : AlgebraicClosure ℚ) = ∏ μ ∈ primitiveRoots q (AlgebraicClosure ℚ), (1 - μ) := by
    have h := eval_one_cyclotomic_prime (R := AlgebraicClosure ℚ) (p := q)
    rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod] at h
    simp only [eval_sub, eval_X, eval_C] at h
    exact h.symm
  have hfac : ∀ μ ∈ primitiveRoots q (AlgebraicClosure ℚ), P.valuation (1 - μ) = P.valuation (1 - ζ) := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ q := (mem_primitiveRoots hq.pos).mp hμ
    obtain ⟨j, hjq, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hμ'.ne_one hq.one_lt (pow_zero ζ)
    have hjκ : (j : IsLocalRing.ResidueField P) ≠ 0 := by
      intro h
      rw [CharP.cast_eq_zero_iff (IsLocalRing.ResidueField P) q] at h
      exact absurd hjq (not_lt.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) h))
    have hgeom : 1 - ζ ^ j = (1 - ζ) * ∑ i ∈ Finset.range j, ζ ^ i := by
      linear_combination geom_sum_mul ζ j
    rw [hgeom, map_mul, valuation_geom_sum_eq_one P hζP hres hjκ, mul_one]
  calc P.valuation (1 - ζ) ^ (q - 1)
      = ∏ μ ∈ primitiveRoots q (AlgebraicClosure ℚ), P.valuation (1 - μ) := by
        rw [Finset.prod_congr rfl hfac, Finset.prod_const, hζ.card_primitiveRoots, Nat.totient_prime hq]
    _ = P.valuation (∏ μ ∈ primitiveRoots q (AlgebraicClosure ℚ), (1 - μ)) := (map_prod _ _ _).symm
    _ = P.valuation (q : AlgebraicClosure ℚ) := by rw [← hprod]

private theorem valuation_sub_one_div_pow_eq_one (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    {π : AlgebraicClosure ℚ} (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ q) :
    P.valuation ((ζ - 1) / π ^ (q + 1)) = 1 := by
  have hq : q.Prime := Fact.out
  have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hn : q ^ 2 - 1 ≠ 0 := by
    have h2 : 2 ≤ q := hq.two_le
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, zero_pow hn] at hπ; exact hq0 hπ.symm
  have hvq0 : P.valuation (q : AlgebraicClosure ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
  have hvπ : P.valuation π ^ (q ^ 2 - 1) = P.valuation (q : AlgebraicClosure ℚ) := by rw [← map_pow, hπ]
  have hv1ζ : P.valuation (ζ - 1) ^ (q - 1) = P.valuation (q : AlgebraicClosure ℚ) := by
    rw [Valuation.map_sub_swap]; exact valuation_one_sub_pow P q hP hζ
  have e : (q + 1) * (q - 1) = q ^ 2 - 1 := by
    have := Nat.sq_sub_sq q 1
    rw [one_pow] at this
    exact this.symm
  have h1 : (P.valuation π ^ (q + 1)) ^ (q - 1) = P.valuation (q : AlgebraicClosure ℚ) := by
    rw [← pow_mul, e, hvπ]
  have hne : P.valuation π ^ (q + 1) ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hπ0)
  have hq1 : q - 1 ≠ 0 := by have := hq.two_le; omega
  rw [map_div₀, map_pow]
  have key : (P.valuation (ζ - 1) * (P.valuation π ^ (q + 1))⁻¹) ^ (q - 1) = 1 := by
    rw [mul_pow, inv_pow, hv1ζ, h1, mul_inv_cancel₀ hvq0]
  have h2 := (pow_eq_one_iff_of_nonneg zero_le' hq1).mp key
  rw [div_eq_mul_inv]
  exact h2

end InertZeta

open InertZeta in
theorem solution
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (hτπ : P.tameCharacter π τ = 1) {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ q = 1) :
    τ ζ = ζ := by
  classical
  have hq : q.Prime := Fact.out
  by_cases hζ1 : ζ = 1
  · rw [hζ1, map_one]
  have hprim : IsPrimitiveRoot ζ q := by
    rw [← orderOf_eq_prime hζ hζ1]; exact IsPrimitiveRoot.orderOf ζ
  haveI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨a, haq, hτζ⟩ := hprim.eq_pow_of_pow_eq_one (ξ := τ ζ) (by rw [← map_pow, hζ, map_one])

  have hτπ' : τ π = π :=
    ((ValuationSubring.tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq
      q P hP π hπ).1 τ).mp hτπ

  have hζP : ζ ∈ P := mem_of_pow_eq_one P hq.pos hζ
  have hres : IsLocalRing.residue P ⟨ζ, hζP⟩ = 1 :=
    ValuationSubring.residue_eq_one_of_pow_prime_pow_eq_one P hq hP (n := 1) (by rw [pow_one]; exact hζ) hζP
  have htame_a : P.tameCharacter (ζ - 1) τ = a :=
    ValuationSubring.tameCharacter_sub_one_eq_natCast P hζP hres hζ1 hτζ.symm

  have hvy := valuation_sub_one_div_pow_eq_one P q hP hπ hprim
  have hyP : (ζ - 1) / π ^ (q + 1) ∈ P := by rw [← P.valuation_le_one_iff, hvy]
  obtain ⟨u, hu⟩ := (P.valuation_eq_one_iff ⟨_, hyP⟩).mpr hvy
  have htame_y : P.tameCharacter ((ζ - 1) / π ^ (q + 1)) τ = 1 := by
    have h := (ValuationSubring.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn P hτ).2 u
    rw [hu] at h
    exact h

  have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hπ0 : π ≠ 0 := by
    intro h
    have hn : q ^ 2 - 1 ≠ 0 := by
      have h2 : 2 ≤ q := hq.two_le
      have : 4 ≤ q ^ 2 := by nlinarith
      omega
    rw [h, zero_pow hn] at hπ; exact hq0 hπ.symm
  have hquot : τ ((ζ - 1) / π ^ (q + 1)) / ((ζ - 1) / π ^ (q + 1)) = τ (ζ - 1) / (ζ - 1) := by
    rw [map_div₀, map_pow, hτπ', div_div_div_cancel_right₀ (pow_ne_zero _ hπ0)]
  have htame_eq : P.tameCharacter ((ζ - 1) / π ^ (q + 1)) τ = P.tameCharacter (ζ - 1) τ := by
    unfold ValuationSubring.tameCharacter
    simp only [hquot]

  have ha1 : ((a : ℕ) : IsLocalRing.ResidueField P) = ((1 : ℕ) : IsLocalRing.ResidueField P) := by
    rw [Nat.cast_one, ← htame_a, ← htame_eq, htame_y]
  haveI := charP_residueField P hq hP
  have hmod : a ≡ 1 [MOD q] := (CharP.natCast_eq_natCast (IsLocalRing.ResidueField P) q).mp ha1
  have ha : a = 1 := by
    unfold Nat.ModEq at hmod
    rwa [Nat.mod_eq_of_lt haq, Nat.mod_eq_of_lt hq.one_lt] at hmod
  rw [← hτζ, ha, pow_one]

#print axioms solution

end S_ValuationSubring_apply_eq_self_of_pow_eq_one_of_tameCharacter_eq_one
end P2MW
export P2MW.S_ValuationSubring_apply_eq_self_of_pow_eq_one_of_tameCharacter_eq_one (solution)
