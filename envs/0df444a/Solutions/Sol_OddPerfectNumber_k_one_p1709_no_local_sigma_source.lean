-- Prove2me | solution 1 for OddPerfectNumber.k_one_p1709_no_local_sigma_source
-- status  : ACCEPTED   (disprove)
-- author  : @Patrick
-- created : 2026-09-18T05:29:05.399249+00:00
-- url     : https://prove2.me/submissions/a9a18063-3e87-4608-b93b-eac96394ee45

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.GroupTheory.OrderOfElement

private instance : Fact (Nat.Prime 1709) := ⟨by decide +kernel⟩

private theorem even_order (x : ZMod 1709) (hx : x ^ 1708 = 1)
    (hn : x ^ 427 ≠ 1) : Even (orderOf x) := by
  have hd : orderOf x ∣ 4 * 427 := orderOf_dvd_of_pow_eq_one hx
  by_contra h
  have hc2 : Nat.Coprime (orderOf x) 2 :=
    Nat.coprime_two_right.mpr (Nat.not_even_iff_odd.mp h)
  have hc4 : Nat.Coprime (orderOf x) 4 := hc2.pow_right 2
  exact hn (orderOf_dvd_iff_pow_eq_one.mp (hc4.dvd_of_dvd_mul_left hd))

theorem solution : ¬ (∀ (sigma a b c e : Nat),
    (sigma = (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 101 ^ i)) →
    (1709 ∣ sigma) → Even (orderOf (3 : ZMod 1709)) →
    Even (orderOf (5 : ZMod 1709)) → Even (orderOf (19 : ZMod 1709)) →
    Even (orderOf (101 : ZMod 1709)) → False) := by
  have hp : (5 : ZMod 1709) ^ 854 = 1 := by decide +kernel
  have hn : (5 : ZMod 1709) - 1 ≠ 0 := by decide +kernel
  have hs : (∑ i ∈ Finset.range 854, (5 : ZMod 1709) ^ i) = 0 := by
    have hg := geom_sum_mul (5 : ZMod 1709) 854
    rw [hp, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right hn
  have hd : 1709 ∣ ∑ i ∈ Finset.range 854, (5 : ℕ) ^ i := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using hs
  intro h
  apply h (∑ i ∈ Finset.range 854, (5 : ℕ) ^ i) 0 853 0 0 (by simp) hd
  · exact even_order _ (by decide +kernel) (by decide +kernel)
  · exact even_order _ (by decide +kernel) (by decide +kernel)
  · exact even_order _ (by decide +kernel) (by decide +kernel)
  · exact even_order _ (by decide +kernel) (by decide +kernel)

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
