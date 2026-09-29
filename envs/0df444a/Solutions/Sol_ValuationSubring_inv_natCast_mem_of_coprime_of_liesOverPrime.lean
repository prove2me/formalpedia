-- Prove2me | solution 1 for ValuationSubring.inv_natCast_mem_of_coprime_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/47086694-d1df-54da-9653-3d2b2b8b3178

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_inv_natCast_mem_of_coprime_of_liesOverPrime

set_option autoImplicit false

namespace ValuationSubring
p2m_export "ValuationSubring" "mem_nonunits_iff valuation_le_one_iff valuation LiesOverPrime"
p2m_open "ValuationSubring"

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem inv_natCast_notMem_of_liesOverPrime [CharZero L] {p : ℕ} (hp : p ≠ 0) (hA : A.LiesOverPrime p) :
    ((p : L))⁻¹ ∉ A := by
  intro h
  have hlt : A.valuation (p : L) < 1 := (A.mem_nonunits_iff).mp hA
  have hle : A.valuation ((p : L))⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr h
  have hp0 : (p : L) ≠ 0 := by exact_mod_cast hp
  rw [map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).mpr hp0)] at hle
  exact (not_lt.mpr hle) hlt

private theorem _root_.ValuationSubring.inv_natCast_mem_of_coprime_of_liesOverPrime {p : ℕ} (hA : A.LiesOverPrime p) {n : ℕ} (hn : n.Coprime p) :
    ((n : L))⁻¹ ∈ A := by
  have hlt : A.valuation (p : L) < 1 := (A.mem_nonunits_iff).mp hA

  have hbez := Nat.gcd_eq_gcd_ab n p
  rw [Nat.Coprime.gcd_eq_one hn] at hbez

  have hn_le : A.valuation (n : L) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A n)
  have hn1 : A.valuation (n : L) = 1 := by
    by_contra hne
    have hnlt : A.valuation (n : L) < 1 := lt_of_le_of_ne hn_le hne
    have h1 : (1 : L) = (n : L) * (n.gcdA p : L) + (p : L) * (n.gcdB p : L) := by
      have := congrArg (Int.cast (R := L)) hbez
      push_cast at this
      exact this
    have ha : A.valuation ((n.gcdA p : L)) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
    have hb : A.valuation ((n.gcdB p : L)) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
    have : A.valuation (1 : L) < 1 := by
      rw [h1]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul]
        calc A.valuation (n : L) * A.valuation (n.gcdA p : L) ≤ A.valuation (n : L) * 1 :=
              mul_le_mul_right ha _
          _ < 1 := by rwa [mul_one]
      · rw [map_mul]
        calc A.valuation (p : L) * A.valuation (n.gcdB p : L) ≤ A.valuation (p : L) * 1 :=
              mul_le_mul_right hb _
          _ < 1 := by rwa [mul_one]
    rw [map_one] at this
    exact lt_irrefl _ this
  apply (A.valuation_le_one_iff _).mp
  rw [map_inv₀, hn1, inv_one]

p2m_export "ValuationSubring" "inv_natCast_mem_of_coprime_of_liesOverPrime"
end ValuationSubring

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L) {p : ℕ} (hA : A.LiesOverPrime p) {n : ℕ} (hn : n.Coprime p) :
    ((n : L))⁻¹ ∈ A :=
  A.inv_natCast_mem_of_coprime_of_liesOverPrime hA hn

end S_ValuationSubring_inv_natCast_mem_of_coprime_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_inv_natCast_mem_of_coprime_of_liesOverPrime (solution)
