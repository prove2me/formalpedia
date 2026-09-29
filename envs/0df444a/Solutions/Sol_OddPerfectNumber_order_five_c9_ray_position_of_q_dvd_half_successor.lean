-- Prove2me | solution 1 for OddPerfectNumber.order_five_c9_ray_position_of_q_dvd_half_successor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T14:05:46.550466+00:00
-- url     : https://prove2.me/submissions/e234f40d-f5e1-41cd-80e1-751af9e29d4d

import Mathlib
import Definitions.Def_opnRightRay
import Definitions.Def_opnLeftRay
import Theorems.Thm_OddPerfectNumber_vieta_phi5_C_nine_ray_coverage
import Theorems.Thm_OddPerfectNumber_opnRightRay_parity_period_three
import Theorems.Thm_OddPerfectNumber_opnLeftRay_parity_period_three
import Theorems.Thm_OddPerfectNumber_opnRightRay_mod_five_period_three
import Theorems.Thm_OddPerfectNumber_opnLeftRay_mod_five_period_three
import Theorems.Thm_OddPerfectNumber_opnLeftRay_order_five_euler_impossible
import Theorems.Thm_OddPerfectNumber_order_five_vieta_C_eq_nine_of_q_dvd_half_successor

open OddPerfectNumber

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000

theorem solution (p q : Nat)
    (hp : p.Prime)
    (hp4 : p % 4 = 1)
    (hq : q.Prime)
    (hsqP : IsSquare (p : ZMod q))
    (hqt : q ∣ (p + 1) / 2)
    (h5 : orderOf (q : ZMod p) = 5) :
    ∃ k : Nat,
      p + 1 = q * k ∧
        ((∃ m : Nat, q = opnRightRay (3 * m) ∧ k = opnRightRay (3 * m + 1)) ∨
         (∃ m : Nat, q = opnLeftRay (3 * m + 3) ∧ k = opnLeftRay (3 * m + 2))) := by
  have h2t : 2 * ((p + 1) / 2) = p + 1 := by omega
  have hp3 : 3 ≤ p := by
    have h2 : p ≠ 2 := by omega
    have h3 : 2 ≤ p := hp.two_le
    omega
  have hqle : q ≤ (p + 1) / 2 := by
    rcases hqt with ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      omega
    calc q = q * 1 := (Nat.mul_one q).symm
      _ ≤ q * r := Nat.mul_le_mul_left q (Nat.one_le_iff_ne_zero.mpr hr0)
      _ = (p + 1) / 2 := hr.symm
  have htltp : (p + 1) / 2 < p := by omega
  have hqltp : q < p := by omega
  have hqplus : q ∣ p + 1 := by
    rcases hqt with ⟨r, hr⟩
    exact ⟨2 * r, by rw [← h2t, hr]; ring⟩
  obtain ⟨k, hk⟩ := hqplus
  have hqpos : 0 < q := hq.pos
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | hk'
    · rw [h0, Nat.mul_zero] at hk
      omega
    · exact hk'
  -- q is odd
  have hqodd : Odd q := by
    refine hq.odd_of_ne_two ?_
    intro hq2
    subst hq2
    rcases hqt with ⟨r, hr⟩
    have hev : Even ((p + 1) / 2) := ⟨r, by omega⟩
    have hodd : ((p + 1) / 2) % 2 = 1 := by
      obtain ⟨c, hc⟩ : ∃ c, p = 4 * c + 1 := by
        refine ⟨p / 4, ?_⟩
        have h := Nat.div_add_mod p 4
        omega
      omega
    have hev0 : ((p + 1) / 2) % 2 = 0 := Nat.even_iff.mp hev
    omega
  -- the C = 9 Vieta quotient for the pair (q, k)
  obtain ⟨k', C, hk', hCEq, hC9⟩ :=
    order_five_vieta_C_eq_nine_of_q_dvd_half_successor p q hp hp4 hq hsqP hqt h5
  have hkk : k' = k := by
    have hmul : q * k' = q * k := by rw [← hk', hk]
    exact Nat.mul_left_cancel hqpos hmul
  have hCEq9 : q ^ 2 + q + k ^ 2 + k + 1 = 9 * (q * k - 1) := by
    rw [hkk, hC9] at hCEq
    exact hCEq
  -- parity pins the odd element to an index divisible by three
  have idxR : ∀ n : Nat, Odd (opnRightRay n) → ∃ m, n = 3 * m := by
    intro n hn
    have hdecomp : 3 * (n / 3) + n % 3 = n := by
      have h := Nat.div_add_mod n 3
      omega
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exact ⟨n / 3, by omega⟩
    · exfalso
      have hev : Even (opnRightRay n) := by
        rw [← hdecomp, h1]
        exact (opnRightRay_parity_period_three (n / 3)).2.1
      exact (Nat.not_even_iff_odd.mpr hn) hev
    · exfalso
      have hev : Even (opnRightRay n) := by
        rw [← hdecomp, h2]
        exact (opnRightRay_parity_period_three (n / 3)).2.2
      exact (Nat.not_even_iff_odd.mpr hn) hev
  have idxL : ∀ n : Nat, Odd (opnLeftRay n) → ∃ m, n = 3 * m := by
    intro n hn
    have hdecomp : 3 * (n / 3) + n % 3 = n := by
      have h := Nat.div_add_mod n 3
      omega
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exact ⟨n / 3, by omega⟩
    · exfalso
      have hev : Even (opnLeftRay n) := by
        rw [← hdecomp, h1]
        exact (opnLeftRay_parity_period_three (n / 3)).2.1
      exact (Nat.not_even_iff_odd.mpr hn) hev
    · exfalso
      have hev : Even (opnLeftRay n) := by
        rw [← hdecomp, h2]
        exact (opnLeftRay_parity_period_three (n / 3)).2.2
      exact (Nat.not_even_iff_odd.mpr hn) hev
  -- the reversed right-ray orientation forces 5 | p
  have hBexcl :
      ¬ (∃ m : Nat, q = opnRightRay (3 * m + 3) ∧ k = opnRightRay (3 * m + 2)) := by
    rintro ⟨m, hqm, hkm⟩
    have hq5 : q % 5 = 1 := by
      rw [hqm]
      have h := (opnRightRay_mod_five_period_three (m + 1)).1
      have hidx : 3 * (m + 1) = 3 * m + 3 := by ring
      rwa [hidx] at h
    have hk5 : k % 5 = 1 := by
      rw [hkm]
      exact (opnRightRay_mod_five_period_three m).2.2
    have hpmod : p % 5 = 0 := by
      have hqk : (q * k) % 5 = 1 := by
        simp [Nat.mul_mod, hq5, hk5]
      have hp1 : (p + 1) % 5 = 1 := by
        rw [hk]
        exact hqk
      omega
    have hp5 : p = 5 := by
      have hdvd : 5 ∣ p := Nat.dvd_of_mod_eq_zero hpmod
      rcases hp.eq_one_or_self_of_dvd 5 hdvd with h1 | h1
      · omega
      · exact h1.symm
    letI : Fact p.Prime := ⟨hp⟩
    have hq0 : (q : ZMod p) ≠ 0 := by
      intro hzero
      have hdiv : p ∣ q := (ZMod.natCast_eq_zero_iff q p).mp hzero
      rcases hq.eq_one_or_self_of_dvd p hdiv with h2 | h2
      · omega
      · omega
    have hord := ZMod.orderOf_dvd_card_sub_one hq0
    rw [h5, hp5] at hord
    omega
  rcases vieta_phi5_C_nine_ray_coverage q k hqpos hkpos hCEq9 with hA | hB | hC | hD
  · rcases hA with ⟨n, hqn, hkn⟩
    obtain ⟨j, hj⟩ := idxR n (by rw [← hqn]; exact hqodd)
    exact ⟨k, hk, Or.inl ⟨j, by rw [hqn, hj], by rw [hkn, hj]⟩⟩
  · rcases hB with ⟨n, hkn, hqn⟩
    exfalso
    obtain ⟨j, hj⟩ := idxR (n + 1) (by rw [← hqn]; exact hqodd)
    have hj1 : 1 ≤ j := by omega
    exact hBexcl ⟨j - 1,
      by rw [hqn, hj]; congr 1; omega,
      by rw [hkn]; congr 1; omega⟩
  · rcases hC with ⟨n, hqn, hkn⟩
    exfalso
    obtain ⟨j, hj⟩ := idxL n (by rw [← hqn]; exact hqodd)
    exact opnLeftRay_order_five_euler_impossible p q k j hp hq hqltp h5 hk
      ⟨by rw [hqn, hj], by rw [hkn, hj]⟩
  · rcases hD with ⟨n, hkn, hqn⟩
    obtain ⟨j, hj⟩ := idxL (n + 1) (by rw [← hqn]; exact hqodd)
    have hj1 : 1 ≤ j := by omega
    exact ⟨k, hk, Or.inr ⟨j - 1,
      by rw [hqn, hj]; congr 1; omega,
      by rw [hkn]; congr 1; omega⟩⟩
