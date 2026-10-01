-- Prove2me | solution 1 for ShorAlgorithms.Reduction.nontrivial_factor_of_even_of_ne_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:19:22.332992+00:00
-- url     : https://prove2.me/submissions/56077129-70bb-494d-8cb7-ad8a34d9eec7

import Mathlib
import Definitions.Def_ShorAlgorithms_Reduction_successEvent
open ShorAlgorithms.Reduction

theorem solution (n : ℕ) (hn : 1 < n) (u : (ZMod n)ˣ)
    (heven : Even (orderOf u)) (hne : (u : ZMod n) ^ (orderOf u / 2) ≠ -1) :
    1 < factorCandidate n u ∧ factorCandidate n u < n := by
  letI : NeZero n := ⟨by omega⟩
  letI : Fact (1 < n) := ⟨hn⟩
  let v : ZMod n := (u : ZMod n) ^ (orderOf u / 2)
  have horder := orderOf_pos u
  have hdiv : orderOf u / 2 * 2 = orderOf u := Nat.div_mul_cancel heven.two_dvd
  have hhalf : orderOf u / 2 ≠ 0 := by omega
  have hv1 : v ≠ 1 := by
    intro hh
    have hu1 : u ^ (orderOf u / 2) = 1 := by
      apply Units.ext
      simpa [v] using hh
    exact pow_ne_one_of_lt_orderOf hhalf (Nat.div_lt_self horder (by norm_num)) hu1
  have hv0 : v ≠ 0 := by
    simpa only [v,Units.val_pow_eq_pow_val] using Units.ne_zero (u ^ (orderOf u / 2))
  have hvsq : v^2 = 1 := by
    dsimp [v]
    rw [←pow_mul,hdiv]
    exact congrArg (fun w : (ZMod n)ˣ => (w : ZMod n)) (pow_orderOf_eq_one u)
  have hval : 1 < v.val := by
    have hpos := ZMod.val_pos.mpr hv0
    have hneval : v.val ≠ 1 := by
      intro hh
      apply hv1
      have he := ZMod.natCast_zmod_val v
      rw [hh,Nat.cast_one] at he
      exact he.symm
    omega
  have hcast : ((v.val-1 : ℕ) : ZMod n) = v-1 := by
    rw [Nat.cast_sub (by omega),ZMod.natCast_zmod_val,Nat.cast_one]
  have hg1 : Nat.gcd (v.val-1) n ≠ 1 := by
    intro hh
    have hc : (v.val-1).Coprime n := hh
    have hu := (ZMod.isUnit_iff_coprime (v.val-1) n).mpr hc
    rw [hcast] at hu
    have hz : (v-1)*(v+1)=(v-1)*0 := by
      calc
        (v-1)*(v+1)=v^2-1 := by ring
        _ = 0 := by rw [hvsq,sub_self]
        _ = (v-1)*0 := by simp
    have hz' : v+1=0 := hu.mul_left_cancel hz
    exact hne (eq_neg_of_add_eq_zero_left hz')
  have hgp : 0 < Nat.gcd (v.val-1) n := Nat.gcd_pos_of_pos_right _ (by omega)
  refine ⟨by change 1 < Nat.gcd (v.val-1) n; omega,?_⟩
  change Nat.gcd (v.val-1) n < n
  exact (Nat.gcd_le_left n (by omega)).trans_lt ((Nat.sub_le _ _).trans_lt (ZMod.val_lt v))
