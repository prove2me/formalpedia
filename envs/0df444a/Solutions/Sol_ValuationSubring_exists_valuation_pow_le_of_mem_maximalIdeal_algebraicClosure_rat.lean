-- Prove2me | solution 1 for ValuationSubring.exists_valuation_pow_le_of_mem_maximalIdeal_algebraicClosure_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/aae8c8c8-a164-5ab7-b2af-62ccf28eb73e

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal
import Theorems.Thm_ValuationSubring_exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_valuation_pow_le_of_mem_maximalIdeal_algebraicClosure_rat

set_option autoImplicit false

namespace R1AF8Card1

theorem isAlgebraic_rat :
    @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ DivisionRing.toRatAlgebra := by
  convert AlgebraicClosure.isAlgebraic ℚ
  rfl
  rfl

theorem exists_prime_mem_nonunits (P : ValuationSubring (AlgebraicClosure ℚ)) (y : P)
    (hy : y ∈ IsLocalRing.maximalIdeal P) (hy0 : y ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : AlgebraicClosure ℚ) ∈ P.nonunits := by
  classical

  set κ := IsLocalRing.ResidueField P
  obtain hprime | hzero := CharP.char_is_prime_or_zero κ (ringChar κ)
  · refine ⟨ringChar κ, hprime, ?_⟩
    rw [ValuationSubring.mem_nonunits_iff]
    have hmem : ((ringChar κ : ℕ) : P) ∈ IsLocalRing.maximalIdeal P := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact CharP.cast_eq_zero κ (ringChar κ)
    have := (ValuationSubring.valuation_lt_one_iff P _).1 hmem
    simpa using this
  ·
    exfalso
    haveI : CharP κ 0 := by rw [← hzero]; exact ringChar.charP κ
    haveI : CharZero κ := CharP.charP_to_charZero κ
    have hyv : P.valuation ((y : AlgebraicClosure ℚ)) < 1 :=
      (ValuationSubring.valuation_lt_one_iff P y).1 hy
    have hy0' : (y : AlgebraicClosure ℚ) ≠ 0 := by
      intro h; exact hy0 (Subtype.ext h)
    obtain ⟨n, hn, c, hc0, hval⟩ :=
      @ValuationSubring.exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic ℚ (AlgebraicClosure ℚ)
        _ _ DivisionRing.toRatAlgebra isAlgebraic_rat P _ hy0'
    have hcv : P.valuation (algebraMap ℚ (AlgebraicClosure ℚ) c) < 1 := by
      rw [← hval, map_pow]
      exact pow_lt_one' hyv hn.ne'
    rw [eq_ratCast, Rat.cast_def, map_div₀] at hcv

    have hunit : ∀ m : ℤ, m ≠ 0 → P.valuation ((m : ℤ) : AlgebraicClosure ℚ) = 1 := by
      intro m hm
      have hres : IsLocalRing.residue P ((m : ℤ) : P) ≠ 0 := by
        rw [map_intCast]; exact Int.cast_ne_zero.2 hm
      rw [Ne, IsLocalRing.residue_eq_zero_iff] at hres
      have h1 : ¬ P.valuation (((m : ℤ) : P) : AlgebraicClosure ℚ) < 1 := by
        rwa [← ValuationSubring.valuation_lt_one_iff P]
      have h2 : P.valuation (((m : ℤ) : P) : AlgebraicClosure ℚ) ≤ 1 := P.valuation_le_one _
      push_cast at h1 h2
      exact le_antisymm h2 (not_lt.1 h1)
    rw [hunit c.num (Rat.num_ne_zero.2 hc0), ← Int.cast_natCast, hunit (c.den : ℤ)
      (by exact_mod_cast c.den_nz), div_one] at hcv
    exact lt_irrefl _ hcv

end R1AF8Card1

open R1AF8Card1 in
theorem solution
    (P : ValuationSubring (AlgebraicClosure ℚ)) :
    ∀ x : AlgebraicClosure ℚ, x ≠ 0 → ∀ y : P, y ∈ IsLocalRing.maximalIdeal P →
      ∃ n : ℕ, P.valuation ((y : AlgebraicClosure ℚ) ^ n) ≤ P.valuation x := by
  intro x hx y hy
  by_cases hy0 : y = 0
  · exact ⟨1, by simp [hy0]⟩
  by_cases hxP : x ∈ P
  swap
  ·
    refine ⟨0, ?_⟩
    rw [pow_zero, map_one]
    exact le_of_lt (not_le.1 fun h => hxP ((P.valuation_le_one_iff x).1 h))
  obtain ⟨q, hq, hqP⟩ := exists_prime_mem_nonunits P y hy hy0
  haveI : Fact q.Prime := ⟨hq⟩
  have hx' : (⟨x, hxP⟩ : P) ≠ 0 := by
    intro h; exact hx (congrArg Subtype.val h)
  obtain ⟨M, d, hd⟩ := ValuationSubring.exists_dvd_pow_of_mem_maximalIdeal P hqP ⟨x, hxP⟩ hx' y hy hy0
  refine ⟨M, ?_⟩
  have hd' : ((y : AlgebraicClosure ℚ)) ^ M = x * (d : AlgebraicClosure ℚ) := by
    have := congrArg Subtype.val hd
    simpa using this
  rw [hd', map_mul]
  exact mul_le_of_le_one_right' (P.valuation_le_one d)

end S_ValuationSubring_exists_valuation_pow_le_of_mem_maximalIdeal_algebraicClosure_rat
end P2MW
export P2MW.S_ValuationSubring_exists_valuation_pow_le_of_mem_maximalIdeal_algebraicClosure_rat (solution)
