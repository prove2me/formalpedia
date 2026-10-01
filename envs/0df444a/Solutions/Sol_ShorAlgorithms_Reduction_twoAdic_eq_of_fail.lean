-- Prove2me | solution 1 for ShorAlgorithms.Reduction.twoAdic_eq_of_fail
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:24:17.392349+00:00
-- url     : https://prove2.me/submissions/f1a7091a-2901-458b-9ad7-9e805cc57ba6

import Mathlib
import Definitions.Def_ShorAlgorithms_Reduction_successEvent
import Definitions.Def_ShorAlgorithms_Reduction_localOrder
open ShorAlgorithms.Reduction

theorem shor_nontrivial_factor (n : ℕ) (hn : 1 < n) (u : (ZMod n)ˣ)
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

private theorem valuation_of_not_half {d r : ℕ} (hr : r ≠ 0) (hd : d ∣ r)
    (hhalf : ¬ d ∣ r/2) : padicValNat 2 d = padicValNat 2 r := by
  obtain ⟨k,rfl⟩ := hd
  have hd0 : d ≠ 0 := by intro h; simp [h] at hr
  have hk0 : k ≠ 0 := by intro h; simp [h] at hr
  have hk : ¬ 2 ∣ k := by
    rintro ⟨l,rfl⟩
    apply hhalf
    refine ⟨l,?_⟩
    rw [show d*(2*l)=(d*l)*2 by ring]
    omega
  rw [padicValNat.mul hd0 hk0,padicValNat.eq_zero_of_not_dvd hk,add_zero]

private theorem local_divides (n : ℕ) (u : (ZMod n)ˣ) (p : ℕ) :
    localOrder n u p ∣ orderOf u :=
  orderOf_map_dvd (Units.map (ZMod.castHom (Nat.ordProj_dvd n p)
    (ZMod (p ^ n.factorization p))).toMonoidHom) u

theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) (u : (ZMod n)ˣ)
    (hfail : ¬ successEvent n u) :
    ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors,
      padicValNat 2 (localOrder n u p) = padicValNat 2 (localOrder n u q) := by
  haveI : NeZero n := ⟨by omega⟩
  have hn2 : ¬ 2 ∣ n := by
    rintro ⟨k,hk⟩
    obtain ⟨j,hj⟩ := hodd
    omega
  by_cases heven : Even (orderOf u)
  · have hneg : (u : ZMod n) ^ (orderOf u / 2) = -1 := by
      by_contra hh
      have hg := shor_nontrivial_factor n hn u heven hh
      exact hfail ⟨heven,hg⟩
    have hval (p : ℕ) (hp : p ∈ n.primeFactors) :
        padicValNat 2 (localOrder n u p) = padicValNat 2 (orderOf u) := by
      obtain ⟨hpp,hpn,hpn0⟩ := Nat.mem_primeFactors.mp hp
      have hpne : p ≠ 2 := by intro hh; subst p; exact hn2 hpn
      have hpgt : 2 < p := by have := hpp.two_le; omega
      have ha := hpp.factorization_pos_of_dvd hpn0 hpn
      have hpow : p ≤ p ^ n.factorization p := by
        simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ p) ha
      haveI : Fact (2 < p ^ n.factorization p) := ⟨hpgt.trans_le hpow⟩
      have hpneg : ((localUnit n u p : (ZMod (p ^ n.factorization p))ˣ) : ZMod (p ^ n.factorization p)) ^
          (orderOf u / 2) = -1 := by
        have hh := congrArg (ZMod.castHom (Nat.ordProj_dvd n p) (ZMod (p ^ n.factorization p))) hneg
        change (ZMod.castHom (Nat.ordProj_dvd n p) (ZMod (p ^ n.factorization p)) (u : ZMod n)) ^ (orderOf u / 2) = -1
        simpa only [map_pow,map_neg,map_one] using hh
      apply valuation_of_not_half (orderOf_pos u).ne' (local_divides n u p)
      intro hd
      have hh : localUnit n u p ^ (orderOf u / 2) = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
      have hh' := congrArg (fun w : (ZMod (p ^ n.factorization p))ˣ => (w : ZMod (p ^ n.factorization p))) hh
      simp only [Units.val_pow_eq_pow_val,Units.val_one] at hh'
      rw [hpneg] at hh'
      exact ZMod.neg_one_ne_one hh'
    intro p hp q hq
    exact (hval p hp).trans (hval q hq).symm
  · have hnorder : ¬ 2 ∣ orderOf u := by
      intro h
      exact heven (even_iff_two_dvd.mpr h)
    have hv (p : ℕ) : padicValNat 2 (localOrder n u p) = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun h => hnorder (h.trans (local_divides n u p)))
    intro p hp q hq
    rw [hv,hv]
