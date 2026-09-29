-- Prove2me | solution 1 for OddPerfectNumber.order_five_phi5_factor_pair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T18:41:20.12438+00:00
-- url     : https://prove2.me/submissions/c497134b-d1ea-486d-9480-67348267e6b7

import Mathlib
import Theorems.Thm_OddPerfectNumber_order_five_phi5_dvd

open OddPerfectNumber

theorem solution (p q : Nat)
    (hp : p.Prime)
    (hp4 : p % 4 = 1)
    (hq : q.Prime)
    (hqt : q ∣ (p + 1) / 2)
    (h5 : orderOf (q : ZMod p) = 5) :
    ∃ k z : Nat,
      p + 1 = q * k ∧ 0 < z ∧
        q ^ 4 + q ^ 3 + q ^ 2 + q + 1 = (q * k - 1) * (q * z - 1) := by
  -- p + 1 = q * k with k = 2 * c: since q | (p+1)/2 and p is odd.
  obtain ⟨c, hc⟩ := hqt
  have ht2 : 2 * ((p + 1) / 2) = p + 1 := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  have hpk : p + 1 = q * (2 * c) := by
    rw [← ht2, hc]
    ring
  -- p | Phi_5(q)
  have hpdvd : p ∣ q ^ 4 + q ^ 3 + q ^ 2 + q + 1 :=
    order_five_phi5_dvd p q hp hq h5
  obtain ⟨U, hU⟩ := hpdvd
  haveI : Fact q.Prime := ⟨hq⟩
  -- modulo q: p = q*k - 1 ≡ -1 and Phi_5(q) = 1 + q*(...) ≡ 1
  have hsum : (p : ZMod q) + 1 = 0 := by
    have h : ((p + 1 : Nat) : ZMod q) = 0 := by
      rw [hpk]
      simp [ZMod.natCast_self]
    simpa using h
  have hphicast : ((q ^ 4 + q ^ 3 + q ^ 2 + q + 1 : Nat) : ZMod q) = 1 := by
    have hq0 : (q : ZMod q) = 0 := ZMod.natCast_self q
    push_cast
    simp [hq0]
  have hpU : (p : ZMod q) * (U : ZMod q) = 1 := by
    have h : ((p * U : Nat) : ZMod q) = 1 := by
      rw [← hU]
      exact hphicast
    simpa using h
  have hpne : (p : ZMod q) ≠ 0 := by
    intro hp0
    have h := hsum
    rw [hp0, zero_add] at h
    exact one_ne_zero h
  have hUz : (U : ZMod q) + 1 = 0 := by
    have hprod : (p : ZMod q) * ((U : ZMod q) + 1) = 0 := by
      calc (p : ZMod q) * ((U : ZMod q) + 1)
          = (p : ZMod q) * (U : ZMod q) + (p : ZMod q) := by ring
        _ = 1 + (p : ZMod q) := by rw [hpU]
        _ = 0 := by simpa [add_comm] using hsum
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h hpne
    · exact h
  -- q | U + 1, i.e. U + 1 = q * z
  have hqU : q ∣ U + 1 := by
    have hz0 : ((U + 1 : Nat) : ZMod q) = 0 := by
      push_cast
      exact hUz
    exact (ZMod.natCast_eq_zero_iff (U + 1) q).mp hz0
  obtain ⟨z, hz⟩ := hqU
  have hzpos : 0 < z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · rw [h, mul_zero] at hz
      omega
    · exact h
  have hU1 : U = q * z - 1 := by omega
  have hk1 : q * (2 * c) - 1 = p := by omega
  refine ⟨2 * c, z, hpk, hzpos, ?_⟩
  rw [hU, hk1, hU1]
