-- Prove2me | solution 1 for ValuationSubring.algebraMap_rat_mem_iff_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/4b71eeb7-51a7-5440-bb25-6b32afaa5b34

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

namespace S12B

section PlaceOverQ

variable {L : Type*} [Field L] (A : ValuationSubring L) {q : ℕ}

theorem valuation_intCast_eq_one (hq : q.Prime) (hA : (q : L) ∈ A.nonunits) {n : ℤ}
    (hn : ¬ (q : ℤ) ∣ n) : A.valuation (n : L) = 1 := by
  have hle : A.valuation (n : L) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A n)
  refine le_antisymm hle ?_
  by_contra hlt
  rw [not_le] at hlt
  rw [ValuationSubring.mem_nonunits_iff] at hA
  have hgcd : Int.gcd (q : ℤ) n = 1 := by
    show (q : ℤ).natAbs.gcd n.natAbs = 1
    rw [Int.natAbs_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hq).mpr (fun h => hn (Int.natCast_dvd.mpr h))
  obtain ⟨a, b, hab⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  have habL : (a : L) * (q : L) + (b : L) * (n : L) = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : L)) hab
  have h1 : A.valuation ((a : L) * (q : L)) < 1 := by
    rw [map_mul]
    calc A.valuation (a : L) * A.valuation (q : L)
        ≤ 1 * A.valuation (q : L) := mul_le_mul_left ((A.valuation_le_one_iff _).mpr (intCast_mem A a)) _
      _ = A.valuation (q : L) := one_mul _
      _ < 1 := hA
  have h2 : A.valuation ((b : L) * (n : L)) < 1 := by
    rw [map_mul]
    calc A.valuation (b : L) * A.valuation (n : L)
        ≤ 1 * A.valuation (n : L) := mul_le_mul_left ((A.valuation_le_one_iff _).mpr (intCast_mem A b)) _
      _ = A.valuation (n : L) := one_mul _
      _ < 1 := hlt
  have := Valuation.map_add_lt A.valuation h1 h2
  rw [habL, map_one] at this
  exact lt_irrefl _ this

variable [CharZero L] [Algebra ℚ L]

theorem algebraMap_rat_mem_iff [Fact q.Prime] (hA : (q : L) ∈ A.nonunits) (x : ℚ) :
    algebraMap ℚ L x ∈ A ↔ x ∈ (Rat.padicValuation q).valuationSubring := by
  have hq : q.Prime := Fact.out
  rw [Valuation.mem_valuationSubring_iff, Rat.padicValuation_le_one_iff]
  have hxL : algebraMap ℚ L x = ((x.num : ℤ) : L) * (((x.den : ℕ) : L))⁻¹ := by
    conv_lhs => rw [← Rat.num_div_den x]
    rw [map_div₀, div_eq_mul_inv, map_intCast, map_natCast]
  constructor
  · intro hx hden

    have hnum : ¬ (q : ℤ) ∣ x.num := by
      intro h
      have h1 : q ∣ x.num.natAbs := Int.natCast_dvd.mp h
      have h2 : q ∣ Nat.gcd x.num.natAbs x.den := Nat.dvd_gcd h1 hden
      rw [x.reduced] at h2
      exact hq.one_lt.ne' (Nat.dvd_one.mp h2)
    have hvnum : A.valuation ((x.num : ℤ) : L) = 1 := valuation_intCast_eq_one A hq hA hnum
    obtain ⟨d, hd⟩ := hden
    have hvden : A.valuation ((x.den : ℕ) : L) < 1 := by
      rw [hd, Nat.cast_mul, map_mul]
      rw [ValuationSubring.mem_nonunits_iff] at hA
      calc A.valuation (q : L) * A.valuation (d : L)
          ≤ A.valuation (q : L) * 1 := mul_le_mul_right ((A.valuation_le_one_iff _).mpr (natCast_mem A d)) _
        _ = A.valuation (q : L) := mul_one _
        _ < 1 := hA
    have hxv : A.valuation (algebraMap ℚ L x) ≤ 1 := (A.valuation_le_one_iff _).mpr hx
    have hmul : algebraMap ℚ L x * ((x.den : ℕ) : L) = ((x.num : ℤ) : L) := by
      have := congrArg (algebraMap ℚ L) (Rat.mul_den_eq_num x)
      rwa [map_mul, map_natCast, map_intCast] at this
    have : A.valuation ((x.num : ℤ) : L) < 1 := by
      rw [← hmul, map_mul]
      calc A.valuation (algebraMap ℚ L x) * A.valuation ((x.den : ℕ) : L)
          ≤ 1 * A.valuation ((x.den : ℕ) : L) := mul_le_mul_left hxv _
        _ = A.valuation ((x.den : ℕ) : L) := one_mul _
        _ < 1 := hvden
    rw [hvnum] at this
    exact lt_irrefl _ this
  · intro hden
    have hvden : A.valuation ((x.den : ℕ) : L) = 1 := by
      have := valuation_intCast_eq_one A hq hA (n := (x.den : ℤ)) (fun h => hden (Int.natCast_dvd_natCast.mp h))
      rwa [Int.cast_natCast] at this
    have hdinv : (((x.den : ℕ) : L))⁻¹ ∈ A := by
      rw [← A.valuation_le_one_iff, map_inv₀, hvden, inv_one]
    rw [hxL]
    exact mul_mem (intCast_mem A x.num) hdinv

end PlaceOverQ

end S12B

end

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime] (hA : A.LiesOverPrime q) (x : ℚ) :
    algebraMap ℚ (AlgebraicClosure ℚ) x ∈ A ↔ x ∈ (Rat.padicValuation q).valuationSubring := by
  exact S12B.algebraMap_rat_mem_iff A hA x

end S_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime (solution)
