-- Prove2me | solution 1 for OddPerfectNumber.odd_order_odd_source_count_le_p
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T20:02:24.709664+00:00
-- url     : https://prove2.me/submissions/5a817ef6-9592-4c16-a2c3-a8c3b08d60e4

import Mathlib

theorem solution {p t n : Nat} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hpt : Not (Dvd.dvd p t)) (hnodd : ¬ Even n) (hord : 1 < orderOf (t : ZMod p))
    (hdiv : Dvd.dvd (orderOf (t : ZMod p)) n) :
    orderOf (t : ZMod p) ≤ n ∧ Dvd.dvd (orderOf (t : ZMod p)) ((p - 1) / 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    subst n
    exact hnodd (by simp)
  have ho : Odd (orderOf (t : ZMod p)) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact hnodd (he.trans_dvd hdiv)
  have hd : orderOf (t : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one (a := (t : ZMod p)) (by simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using hpt)
  refine ⟨Nat.le_of_dvd hn hdiv, ?_⟩
  apply ho.coprime_two_right.dvd_mul_left.mp
  have heq : 2 * ((p - 1) / 2) = p - 1 := by omega
  rwa [heq]
