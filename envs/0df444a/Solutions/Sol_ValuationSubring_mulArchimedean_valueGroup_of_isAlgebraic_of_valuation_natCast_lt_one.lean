-- Prove2me | solution 1 for ValuationSubring.mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/21c13868-7331-5403-840d-7e082990aff3

import Mathlib
import Theorems.Thm_ValuationSubring_exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one

open scoped Classical

namespace P2mR1W0arch

section ValueGroup

variable {K : Type*} [Field K] (A : ValuationSubring K)
variable [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]

theorem exists_pow_valuation_eq_valuation_prime_zpow {p : ℕ} (hp : p.Prime)
    (hAp : A.valuation (p : K) < 1) {x : K} (hx : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℤ, A.valuation x ^ n = A.valuation (p : K) ^ k :=
  ValuationSubring.exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic A hp hAp hx

theorem mulArchimedean_valueGroup {p : ℕ} (hp : p.Prime) (hAp : A.valuation (p : K) < 1) :
    MulArchimedean A.ValueGroup := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  set π := A.valuation (p : K) with hπ
  have hp0 : π ≠ 0 := by
    rw [hπ, ne_eq, Valuation.zero_iff]
    exact_mod_cast hp.ne_zero
  have hπpos : 0 < π := zero_lt_iff.mpr hp0

  have hneg : ∀ k : ℤ, 1 < π ^ k → k < 0 := by
    intro k hk
    by_contra hk0
    push Not at hk0
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    rw [zpow_natCast] at hk
    exact absurd hk (not_lt.mpr (pow_le_one₀ zero_le' hAp.le))
  refine ⟨fun x y hy => ?_⟩
  by_cases hx1 : x ≤ 1
  · exact ⟨1, hx1.trans (by rw [pow_one]; exact hy.le)⟩
  push Not at hx1
  obtain ⟨g, rfl⟩ := A.valuation_surjective x
  obtain ⟨h, rfl⟩ := A.valuation_surjective y
  have hg0 : g ≠ 0 := by rintro rfl; simp at hx1
  have hh0 : h ≠ 0 := by rintro rfl; simp at hy
  obtain ⟨a, ha, k, hk⟩ := exists_pow_valuation_eq_valuation_prime_zpow A hp hAp hg0
  obtain ⟨b, hb, l, hl⟩ := exists_pow_valuation_eq_valuation_prime_zpow A hp hAp hh0
  have hk0 : k < 0 := hneg k (by rw [← hk]; exact one_lt_pow₀ hx1 ha.ne')
  have hl0 : l < 0 := hneg l (by rw [← hl]; exact one_lt_pow₀ hy hb.ne')
  refine ⟨b * k.natAbs, ?_⟩

  apply le_of_pow_le_pow_left₀ ha.ne' zero_le'
  have hexp : l * ((k.natAbs : ℤ) * a) ≤ k := by
    have hka : (k.natAbs : ℤ) ≤ (k.natAbs : ℤ) * a := by
      have : (1 : ℤ) ≤ a := by exact_mod_cast ha
      nlinarith [Int.natCast_nonneg k.natAbs]
    have hkabs : (k.natAbs : ℤ) = -k := by omega
    nlinarith
  calc A.valuation g ^ a = π ^ k := hk
    _ ≤ π ^ (l * ((k.natAbs : ℤ) * a)) := zpow_le_zpow_right_of_le_one₀ hπpos hAp.le hexp
    _ = ((A.valuation h ^ b) ^ k.natAbs) ^ a := by
        rw [hl, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
    _ = (A.valuation h ^ (b * k.natAbs)) ^ a := by rw [pow_mul]

end ValueGroup

end P2mR1W0arch

theorem solution
    {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (A : ValuationSubring K) {p : ℕ} (hp : p.Prime) (hAp : A.valuation (p : K) < 1) :
    MulArchimedean A.ValueGroup :=
  P2mR1W0arch.mulArchimedean_valueGroup A hp hAp

end S_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one
end P2MW
export P2MW.S_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one (solution)
