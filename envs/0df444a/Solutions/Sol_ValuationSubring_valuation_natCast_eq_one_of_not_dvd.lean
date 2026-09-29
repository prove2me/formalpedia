-- Prove2me | solution 1 for ValuationSubring.valuation_natCast_eq_one_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/2e6f6334-8a54-52a3-aa34-87ab3ff44895

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_valuation_natCast_eq_one_of_not_dvd

set_option autoImplicit false

theorem solution {K : Type*} [Field K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {n : ℕ} (hqn : ¬ q ∣ n) : A.valuation (n : K) = 1 := by
  have hleZ : ∀ a : ℤ, A.valuation (a : K) ≤ 1 := fun a =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A a)
  have hle : ∀ m : ℕ, A.valuation (m : K) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (natCast_mem A m)
  refine le_antisymm (hle n) ?_
  by_contra hlt
  have hnlt : A.valuation (n : K) < 1 := lt_of_le_of_ne (hle n) (fun h => hlt h.ge)
  have hcop : Nat.Coprime q n := (hq.coprime_iff_not_dvd).mpr hqn
  have hbez : ((Nat.gcd q n : ℤ) : K)
      = (q : K) * ((Nat.gcdA q n : ℤ) : K) + (n : K) * ((Nat.gcdB q n : ℤ) : K) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : K)) (Nat.gcd_eq_gcd_ab q n)
  rw [hcop.gcd_eq_one] at hbez
  push_cast at hbez
  have h1 : A.valuation 1
      ≤ max (A.valuation ((q : K) * ((Nat.gcdA q n : ℤ) : K)))
          (A.valuation ((n : K) * ((Nat.gcdB q n : ℤ) : K))) := by
    rw [show (1 : K) = (q : K) * ((Nat.gcdA q n : ℤ) : K)
        + (n : K) * ((Nat.gcdB q n : ℤ) : K) from hbez]
    exact A.valuation.map_add _ _
  have hterm1 : A.valuation ((q : K) * ((Nat.gcdA q n : ℤ) : K)) < 1 := by
    rw [map_mul]
    calc A.valuation (q : K) * A.valuation ((Nat.gcdA q n : ℤ) : K)
        ≤ A.valuation (q : K) * 1 := mul_le_mul' le_rfl (hleZ _)
      _ = A.valuation (q : K) := mul_one _
      _ < 1 := hA
  have hterm2 : A.valuation ((n : K) * ((Nat.gcdB q n : ℤ) : K)) < 1 := by
    rw [map_mul]
    calc A.valuation (n : K) * A.valuation ((Nat.gcdB q n : ℤ) : K)
        ≤ A.valuation (n : K) * 1 := mul_le_mul' le_rfl (hleZ _)
      _ = A.valuation (n : K) := mul_one _
      _ < 1 := hnlt
  rw [map_one] at h1
  exact absurd h1 (not_le.mpr (max_lt hterm1 hterm2))

end S_ValuationSubring_valuation_natCast_eq_one_of_not_dvd
end P2MW
export P2MW.S_ValuationSubring_valuation_natCast_eq_one_of_not_dvd (solution)
