-- Prove2me | solution 1 for OddGoldbach19.prime_pair_count_refined_five
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T17:19:48.095483+00:00
-- url     : https://prove2.me/submissions/1f9f3b6f-38e7-4baf-aa97-ca67b38ca0c5

import Mathlib
import Theorems.Thm_OddGoldbach19_prime_pair_count_base_five
import Theorems.Thm_OddGoldbach19_reciprocal_denominator_five_bounds
import Theorems.Thm_PrimePairSieve_sieve_constants_certificate
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RefinedPair

lemma sqrt_ge_log_cube (x : ℝ) (hx : 0<x) (hl : 40 ≤ Real.log x) :
    Real.log x^3 ≤ Real.sqrt x := by
  have hp := Real.pow_div_factorial_le_exp (Real.log x/2) (show 0≤Real.log x/2 by linarith) 6
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_ofNat] at hp
  have h3 : (40:ℝ)^3 ≤ Real.log x^3 := pow_le_pow_left₀ (by norm_num) hl 3
  have he : Real.exp (Real.log x/2)=Real.sqrt x := by
    rw [← Real.log_sqrt hx.le, Real.exp_log (Real.sqrt_pos.mpr hx)]
  rw [he] at hp
  have hpoly : Real.log x^3 ≤ (Real.log x/2)^6/720 := by
    nlinarith [mul_nonneg (show 0≤Real.log x^3 by positivity)
      (show 0≤Real.log x^3-46080 by norm_num at h3; linarith)]
  exact hpoly.trans hp

lemma absorb (L C K x e a b : ℝ) (hL : 40≤L) (hC : 1.25≤C) (hK : 1≤K)
    (hx : x=e^2) (he : L^3≤e) (ha : 0≤a) (hab : a≤b)
    (hb : b≤6) (hgap : 0.1≤b-a) :
    8*C*K*x/(L*(L+b))+e/2 ≤ 8*C*K*x/(L*(L+a)) := by
  have hL0 : 0<L := by linarith
  have he0 : 0<e := lt_of_lt_of_le (by positivity) he
  have hx0 : 0≤x := by rw [hx]; positivity
  have hb0 : 0≤b := ha.trans hab
  have hd : 0<L*(L+a)*(L+b) := by positivity
  have hsmall : (L+a)*(L+b) ≤ 2*L^2 := by
    have h1 : L+a ≤ 1.15*L := by linarith
    have h2 : L+b ≤ 1.15*L := by linarith
    have hm := mul_le_mul h1 h2 (by linarith) (by linarith)
    nlinarith [sq_nonneg L]
  have hcoef : 1≤8*C*K*(b-a) := by
    have h1 : (10:ℝ)≤8*C*K := by
      have := mul_le_mul_of_nonneg_left hK (show 0≤8*C by linarith)
      nlinarith
    have hh := mul_le_mul h1 hgap (by norm_num : (0:ℝ)≤0.1) (by linarith : 0≤8*C*K)
    norm_num at hh
    exact hh
  have hpoly : (e/2)*(L*(L+a)*(L+b)) ≤ x := by
    calc
      _ = (e/2*L)*((L+a)*(L+b)) := by ring
      _ ≤ (e/2*L)*(2*L^2) := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = e*L^3 := by ring
      _ ≤ e*e := mul_le_mul_of_nonneg_left he he0.le
      _ = x := by rw [hx]; ring
  have herr : e/2 ≤ 8*C*K*x*(b-a)/(L*(L+a)*(L+b)) := by
    rw [le_div_iff₀ hd]
    have hh := mul_le_mul_of_nonneg_right hcoef hx0
    nlinarith
  have hdif : 8*C*K*x/(L*(L+a))-8*C*K*x/(L*(L+b)) =
      8*C*K*x*(b-a)/(L*(L+a)*(L+b)) := by
    field_simp
    ring
  linarith

lemma cutoff_error (x : ℝ) (hx : 0<x) (hl : 40≤Real.log x) :
    Real.sqrt x/Real.sqrt 5+1 ≤ Real.sqrt x/2 := by
  have he := sqrt_ge_log_cube x hx hl
  have h3 : (40:ℝ)^3 ≤ Real.log x^3 := pow_le_pow_left₀ (by norm_num) hl 3
  have hs5 : (2.2:ℝ) ≤ Real.sqrt 5 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hq : Real.sqrt x/Real.sqrt 5 ≤ Real.sqrt x/2.2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hs5
  norm_num at h3
  have hq' : Real.sqrt x/Real.sqrt 5 ≤ (5/11)*Real.sqrt x := by
    convert hq using 1 <;> ring
  calc
    _ ≤ (5/11)*Real.sqrt x+1 := by linarith only [hq']
    _ ≤ Real.sqrt x/2 := by linarith only [he,h3]

end RefinedPair

theorem solution (x d : ℕ) (hx : 5≤x)
    (hd0 : 0<d) (hd : 2∣d) (hl : 40≤Real.log (x:ℝ)) :
    (∑ n ∈ Finset.range (x+1),
      if Nat.Prime n ∧ Nat.Prime (n+d) ∧ n+d≤x then (1:ℝ) else 0) ≤
    8*TaoFivePrimes.twinPrimeConstant*
      (∏ p ∈ d.primeFactors, if 2<p then ((p:ℝ)-1)/((p:ℝ)-2) else 1)*(x:ℝ)/
        (Real.log (x:ℝ)*(Real.log (x:ℝ)+4)) ∧
    (100≤Real.log (x:ℝ) →
      (∑ n ∈ Finset.range (x+1),
        if Nat.Prime n ∧ Nat.Prime (n+d) ∧ n+d≤x then (1:ℝ) else 0) ≤
      8*TaoFivePrimes.twinPrimeConstant*
        (∏ p ∈ d.primeFactors, if 2<p then ((p:ℝ)-1)/((p:ℝ)-2) else 1)*(x:ℝ)/
          (Real.log (x:ℝ)*(Real.log (x:ℝ)+5.5))) := by
  have hx0 : (0:ℝ)<x := by exact_mod_cast (show 0<x by omega)
  let K : ℝ := ∏ p ∈ d.primeFactors, if 2<p then ((p:ℝ)-1)/((p:ℝ)-2) else 1
  let S : ℝ := ∑ n ∈ Finset.Icc 1 ⌊Real.sqrt (x:ℝ)/Real.sqrt 5⌋₊,
    (if Squarefree n then ∏ p ∈ n.primeFactors,
      if p=2 then (1:ℝ) else 2/((p:ℝ)-2) else 0)/
      (1+(n:ℝ)/(Real.sqrt (x:ℝ)/Real.sqrt 5))
  have hK : 1≤K := by
    apply Finset.one_le_prod
    intro p hp
    split_ifs with h
    · have hpR : (2:ℝ)<p := by exact_mod_cast h
      rw [le_div_iff₀ (by linarith : (0:ℝ)<(p:ℝ)-2)]
      linarith
    · exact le_rfl
  rcases PrimePairSieve.sieve_constants_certificate with ⟨hC,-,-,-⟩
  have hbase := OddGoldbach19.prime_pair_count_base_five x d hx hd0 hd
  change _ ≤ K*(x:ℝ)/S+Real.sqrt (x:ℝ)/Real.sqrt 5+1 at hbase
  have hsum (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤6) (hgap : 0.1≤b-a)
      (hden : Real.log (x:ℝ)*(Real.log (x:ℝ)+b) ≤ 8*TaoFivePrimes.twinPrimeConstant*S) :
      K*(x:ℝ)/S+Real.sqrt (x:ℝ)/Real.sqrt 5+1 ≤
      8*TaoFivePrimes.twinPrimeConstant*K*x/(Real.log (x:ℝ)*(Real.log (x:ℝ)+a)) := by
    have hb0 : 0≤b := ha.trans hab
    have hD : 0<Real.log (x:ℝ)*(Real.log (x:ℝ)+b) := by positivity
    have hS : 0<S := by nlinarith
    have hp : K*(x:ℝ)/S ≤ 8*TaoFivePrimes.twinPrimeConstant*K*x/
        (Real.log (x:ℝ)*(Real.log (x:ℝ)+b)) := by
      rw [div_le_div_iff₀ hS hD]
      have hh := mul_le_mul_of_nonneg_left hden (show 0≤K*(x:ℝ) by positivity)
      nlinarith
    have herr := RefinedPair.cutoff_error (x:ℝ) hx0 hl
    have habs := RefinedPair.absorb (Real.log (x:ℝ)) TaoFivePrimes.twinPrimeConstant K x
      (Real.sqrt (x:ℝ)) a b hl hC hK (Real.sq_sqrt hx0.le).symm
      (RefinedPair.sqrt_ge_log_cube (x:ℝ) hx0 hl) ha hab hb hgap
    linarith
  constructor
  · exact hbase.trans (hsum 4 4.5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ((OddGoldbach19.reciprocal_denominator_five_bounds (x:ℝ) hx0 hl).1))
  · intro hl100
    exact hbase.trans (hsum 5.5 5.6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ((OddGoldbach19.reciprocal_denominator_five_bounds (x:ℝ) hx0 hl).2 hl100))
#print axioms solution
