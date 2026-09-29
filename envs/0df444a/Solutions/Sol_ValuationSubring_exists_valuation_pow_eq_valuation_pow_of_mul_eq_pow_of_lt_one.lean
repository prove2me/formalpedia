-- Prove2me | solution 1 for ValuationSubring.exists_valuation_pow_eq_valuation_pow_of_mul_eq_pow_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/fee87578-0c73-5c7f-b3dc-256fd48e279d

import Mathlib
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_ValuationSubring_exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_valuation_pow_eq_valuation_pow_of_mul_eq_pow_of_lt_one

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime]
    (ϖ : AlgebraicClosure ℚ) (eK : ℕ) (heK : 1 ≤ eK) (ε : AlgebraicClosure ℚ) (hε : A.valuation ε = 1)
    (hqϖ : ((q : ℕ) : AlgebraicClosure ℚ) = ϖ ^ eK * ε)
    (E : ℕ) (hE : 1 ≤ E) (a b : AlgebraicClosure ℚ)
    (ha : A.valuation a < 1) (hb : A.valuation b < 1)
    (hab : A.valuation a * A.valuation b = A.valuation ϖ ^ E) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ p : ℕ, 1 ≤ p ∧ p + 1 ≤ r * E ∧ A.valuation a ^ r = A.valuation ϖ ^ p := by

  have hE0 : E ≠ 0 := by omega

  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : eK ≠ 0), zero_mul] at hqϖ
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) hqϖ
  have hv0 : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ0
  have hvpos : 0 < A.valuation ϖ := zero_lt_iff.mpr hv0
  have hv1 : A.valuation ϖ < 1 := by
    by_contra h1
    rw [not_lt] at h1
    have hE1 : 1 ≤ A.valuation ϖ ^ E := one_le_pow₀ h1
    rw [← hab] at hE1
    have hlt : A.valuation a * A.valuation b < 1 := by
      calc A.valuation a * A.valuation b ≤ A.valuation a * 1 := mul_le_mul_right hb.le _
        _ = A.valuation a := mul_one _
        _ < 1 := ha
    exact absurd (lt_of_le_of_lt hE1 hlt) (lt_irrefl _)

  have hva0 : A.valuation a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hab
    exact pow_ne_zero E hv0 hab.symm
  have ha0 : a ≠ 0 := fun h => hva0 (by rw [h, map_zero])
  have hapos : 0 < A.valuation a := zero_lt_iff.mpr hva0
  have halow : A.valuation ϖ ^ E < A.valuation a := by
    rw [← hab]
    calc A.valuation a * A.valuation b < A.valuation a * 1 := mul_lt_mul_of_pos_left hb hapos
      _ = A.valuation a := mul_one _

  obtain ⟨m, hm, kk, hk⟩ := A.exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic hv0 hv1 ha0
  have hk0 : 0 < kk := by
    rw [← zpow_lt_one_iff_right_of_lt_one₀ hvpos hv1, ← hk]
    exact pow_lt_one₀ zero_le' ha hm.ne'
  have hkE : kk < (m * E : ℕ) := by
    rw [← zpow_lt_zpow_iff_right_of_lt_one₀ hvpos hv1, ← hk, zpow_natCast, pow_mul']
    exact pow_lt_pow_left₀ halow zero_le' hm.ne'
  refine ⟨m, hm, kk.toNat, by omega, by omega, ?_⟩
  rw [hk, ← zpow_natCast, Int.toNat_of_nonneg hk0.le]

end S_ValuationSubring_exists_valuation_pow_eq_valuation_pow_of_mul_eq_pow_of_lt_one
end P2MW
export P2MW.S_ValuationSubring_exists_valuation_pow_eq_valuation_pow_of_mul_eq_pow_of_lt_one (solution)
