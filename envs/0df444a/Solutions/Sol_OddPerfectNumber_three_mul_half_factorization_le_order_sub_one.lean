-- Prove2me | solution 1 for OddPerfectNumber.three_mul_half_factorization_le_order_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T16:21:47.720879+00:00
-- url     : https://prove2.me/submissions/c964a5c1-2aaf-45bc-8b4b-ee486d7773b4

import Mathlib
import Theorems.Thm_OddPerfectNumber_brent_cohen_te_riele_sigma_exp_bound
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_zmod_pow_eq_one_iff

open OddPerfectNumber

theorem solution (p q : Nat)
    (hp : p.Prime)
    (hp4 : p % 4 = 1)
    (hq : q.Prime)
    (hqt : q ∣ (p + 1) / 2) :
    3 * ((p + 1) / 2).factorization q ≤ orderOf (q : ZMod p) - 1 := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hp4
  have hqpos : 0 < q := hq.pos
  have htpos : 0 < (p + 1) / 2 := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  have htne : (p + 1) / 2 ≠ 0 := htpos.ne'
  have ht2 : 2 * ((p + 1) / 2) = p + 1 := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  have hqle : q ≤ (p + 1) / 2 := Nat.le_of_dvd htpos hqt
  have hqlt : q < p := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  -- t = (p+1)/2 is odd, so q = 2 is impossible
  have htodd : Odd ((p + 1) / 2) := by
    obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 1 := by
      refine ⟨p / 4, ?_⟩
      have hmod := Nat.div_add_mod p 4
      omega
    refine ⟨k, ?_⟩
    have hp1 : p + 1 = 2 * (2 * k + 1) := by omega
    omega
  have hnot2 : ¬ 2 ∣ (p + 1) / 2 := by
    intro hd
    obtain ⟨k, hk⟩ := htodd
    obtain ⟨c, hc⟩ := hd
    omega
  have hq2 : q ≠ 2 := by
    intro h
    subst q
    exact hnot2 hqt
  -- exact q-adic exponent of p + 1 = 2 * ((p+1)/2)
  have hqnotdvd2 : ¬ q ∣ 2 := by
    intro hdiv
    have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hge : 2 ≤ q := hq.two_le
    omega
  have h2fac : (2 : Nat).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqnotdvd2
  have hptfac : (p + 1).factorization q = ((p + 1) / 2).factorization q := by
    -- rewrite only the left-hand side: a plain `rw` would also rewrite the
    -- nested `p + 1` inside `(p + 1) / 2`
    conv_lhs => rw [← ht2]
    have hfac := Nat.factorization_mul (a := 2) (b := (p + 1) / 2)
      (by norm_num : (2 : Nat) ≠ 0) htne
    rw [hfac]
    simp only [Finsupp.add_apply, h2fac, zero_add]
  have hp1ne : p + 1 ≠ 0 := by omega
  have hqpow : q ^ (((p + 1) / 2).factorization q) ∣ p + 1 :=
    (hq.pow_dvd_iff_le_factorization hp1ne).mpr (le_of_eq hptfac.symm)
  have hqpow_exact : ¬ q ^ (((p + 1) / 2).factorization q + 1) ∣ p + 1 := by
    intro hdiv
    have hle := (hq.pow_dvd_iff_le_factorization hp1ne).mp hdiv
    rw [hptfac] at hle
    omega
  have hrpos : 1 ≤ ((p + 1) / 2).factorization q :=
    hq.factorization_pos_of_dvd htne hqt
  -- multiplicative order of q modulo p
  haveI : Fact p.Prime := ⟨hp⟩
  have hqmodp : (q : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ q := (ZMod.natCast_eq_zero_iff q p).mp h
    have hle : p ≤ q := Nat.le_of_dvd hqpos hdvd
    omega
  have hhpos : 0 < orderOf (q : ZMod p) := by
    have hdvd : orderOf (q : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hqmodp
    have hp1pos : 0 < p - 1 := by
      have h2 : 2 ≤ p := hp.two_le
      omega
    exact Nat.pos_of_dvd_of_pos hdvd hp1pos
  have hpow : (q : ZMod p) ^ orderOf (q : ZMod p) = 1 := pow_orderOf_eq_one _
  have hpdvd_qsub : p ∣ q ^ orderOf (q : ZMod p) - 1 :=
    (zmod_pow_eq_one_iff (q := p) (p := q) (n := orderOf (q : ZMod p)) hq.one_le).mp hpow
  have hgeom :
      (∑ i ∈ Finset.range (orderOf (q : ZMod p)), q ^ i) * (q - 1)
        = q ^ orderOf (q : ZMod p) - 1 :=
    geom_mul_sub_one q (orderOf (q : ZMod p)) hq.one_le
  have hpdvd_prod :
      p ∣ (∑ i ∈ Finset.range (orderOf (q : ZMod p)), q ^ i) * (q - 1) := by
    rw [hgeom]
    exact hpdvd_qsub
  have hpnotdvd : ¬ p ∣ q - 1 := by
    intro hd
    have h1 : 0 < q - 1 := by
      have h2 : 2 ≤ q := hq.two_le
      omega
    have hle : p ≤ q - 1 := Nat.le_of_dvd h1 hd
    omega
  have hsum : p ∣ ∑ i ∈ Finset.range (orderOf (q : ZMod p)), q ^ i := by
    rcases hp.dvd_mul.mp hpdvd_prod with h | h
    · exact h
    · exact absurd h hpnotdvd
  have hsigma :
      p ∣ ∑ i ∈ Finset.range ((orderOf (q : ZMod p) - 1) + 1), q ^ i := by
    rw [show orderOf (q : ZMod p) - 1 + 1 = orderOf (q : ZMod p) by omega]
    exact hsum
  exact brent_cohen_te_riele_sigma_exp_bound p q
      (orderOf (q : ZMod p) - 1) (((p + 1) / 2).factorization q)
      hp hq hp2 hq2 (by omega : p ≠ q) hrpos hqpow hqpow_exact hsigma
