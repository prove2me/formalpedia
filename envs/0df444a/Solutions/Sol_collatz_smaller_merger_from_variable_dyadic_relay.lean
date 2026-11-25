-- Prove2me | solution 1 for collatz_smaller_merger_from_variable_dyadic_relay
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:04:41.259126+00:00
-- url     : https://prove2.me/submissions/902557d9-bd27-4e5d-9d3f-11efad37392d

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Factorization.Basic

private theorem stepEven (n : ℕ) (h : n % 2 = 0) : collatzStep n = n / 2 := by
  rw [collatzStep, if_pos (Nat.even_iff.mpr h)]

private theorem stepOdd (n : ℕ) (h : n % 2 = 1) : collatzStep n = 3*n+1 := by
  rw [collatzStep, if_neg (by rw [Nat.even_iff, h]; decide)]

private theorem trailingOnesRun (L q : ℕ) (hq : 0 < q) :
    collatzStep^[2*L] (2^L*q-1) = 3^L*q-1 := by
  induction L generalizing q with
  | zero => simp
  | succ L ih =>
    have hp : 0 < 2^L*q := Nat.mul_pos (Nat.two_pow_pos _) hq
    have hh : 2^(L+1)*q = 2*(2^L*q) := by rw [pow_succ]; ring
    have odd : (2^(L+1)*q-1) % 2 = 1 := by rw [hh]; omega
    have second : (3*(2^(L+1)*q-1)+1) % 2 = 0 := by rw [hh]; omega
    have hx : 2^L*(3*q) = 3*(2^L*q) := by ring
    have firstPair : collatzStep^[2] (2^(L+1)*q-1) = 2^L*(3*q)-1 := by
      rw [Function.iterate_succ_apply, Function.iterate_one, stepOdd _ odd, stepEven _ second,
        hh, hx]
      omega
    have hpow : 3^L*(3*q) = 3^(L+1)*q := by rw [pow_succ]; ring
    rw [show 2*(L+1) = 2*L+2 by omega, Function.iterate_add_apply, firstPair,
      ih (3*q) (by omega), hpow]

private theorem powerHalvings (s k : ℕ) : collatzStep^[s] (2^s*k) = k := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hf : 2^(s+1)*k = 2*(2^s*k) := by rw [pow_succ]; ring
    rw [Function.iterate_succ_apply, hf, stepEven _ (by omega)]
    simpa using ih

private theorem oddStepThenHalves (x y a : ℕ) (ha : 0<a)
    (h : 3*x+1=2^a*y) : collatzStep^[a+1] x=y := by
  have he : (3*x+1)%2=0 := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
    have heq : 2^(j+1)*y=2*(2^j*y) := by rw [pow_succ]; ring
    rw [h,heq]
    omega
  have ho : x%2=1 := by omega
  rw [Function.iterate_add_apply,Function.iterate_one,stepOdd _ ho,h,powerHalvings]

/-- Two separated pairs of halvings give a family of smaller visitors
through a relay at height four to a variable power times the first
shortcut value. All clocks in the conclusion are ordinary clocks. -/
private theorem collatz_coalescence_from_dyadic_relay (n s r : ℕ) (hodd : n%2=1)
    (hs : 0<s) (hr : 0<r)
    (hmargin : 2^r*(16*4^s)≤3^(r+2))
    (hdiv : 3^(r+3) ∣ 16*4^s*(3*n+1)-10) :
    ∃ k : ℕ, 0<k ∧ k<n ∧ collatzStep^[2] n=collatzStep^[2*r+2*s+8] k := by
  let A := 4^s*(3*n+1)
  let p := (3*n+1)/2
  obtain ⟨z,hz⟩ := hdiv
  rw [Nat.mul_assoc] at hz
  change 16*A-10=3^(r+3)*z at hz
  have hA : 0<A := Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
  have hmain : 16*A=3^(r+3)*z+10 := by omega
  have hzpos : 0<z := by
    by_contra! hzero
    rw [Nat.eq_zero_of_le_zero hzero,mul_zero] at hmain
    omega
  have hm : 3^(r+3)*z=27*(3^r*z) := by rw [pow_add]; norm_num; ring
  let u := (A-1)/3
  have hu : 3*u+1=A := by dsimp [u]; omega
  let v := (4*u-1)/3
  have hv : 3*v+1=4*u := by dsimp [v]; omega
  let w := 3^r*z-1
  have hw : 3*w+1=4*v := by
    dsimp [w]
    have hp : 0<3^r*z := Nat.mul_pos (Nat.pow_pos (by decide)) hzpos
    omega
  have hpn : 3*n+1=2*p := by dsimp [p]; omega
  have hup : 3*u+1=2^(2*s+1)*p := by
    rw [hu]
    dsimp [A]
    rw [hpn,show (4:ℕ)=2^2 by decide,←pow_mul,pow_succ]
    ring
  have hright : 3^(r+3)*(n+1)>3^(r+2)*(3*n+1) := by
    rw [show r+3=(r+2)+1 by omega,pow_succ,Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (Nat.pow_pos (by decide))
  have hbound : 3^(r+3)*(2^r*z)<3^(r+3)*(n+1) := calc
    _ = 2^r*(3^(r+3)*z) := by ring
    _ ≤ 2^r*(16*A) := Nat.mul_le_mul_left _ (by omega)
    _ = (2^r*(16*4^s))*(3*n+1) := by dsimp [A]; ring
    _ ≤ 3^(r+2)*(3*n+1) := Nat.mul_le_mul_right _ hmargin
    _ < _ := hright
  have hstay : 2^r*z<n+1 :=
    (Nat.mul_lt_mul_left (Nat.pow_pos (by decide : 0<(3:ℕ)))).mp hbound
  let k := 2^r*z-1
  have h2r : 2≤2^r :=
    Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega : 1≤r)
  have hpos : 0<k := by
    have hlow : 2^r≤2^r*z := Nat.le_mul_of_pos_right _ hzpos
    dsimp [k]
    omega
  have hlt : k<n := by dsimp [k]; omega
  have hfirst : collatzStep^[2*r] k=w := trailingOnesRun r z hzpos
  have hwv : collatzStep^[3] w=v := oddStepThenHalves w v 2 (by decide) hw
  have hvu : collatzStep^[3] v=u := oddStepThenHalves v u 2 (by decide) hv
  have hup' : collatzStep^[2*s+2] u=p := oddStepThenHalves u p (2*s+1) (by omega) hup
  have hn' : collatzStep^[2] n=p := oddStepThenHalves n p 1 (by decide) (by simpa using hpn)
  refine ⟨k,hpos,hlt,?_⟩
  rw [hn',show 2*r+2*s+8=(2*s+2)+(3+(3+2*r)) by omega,
    Function.iterate_add_apply _ (2*s+2) (3+(3+2*r)),
    Function.iterate_add_apply _ 3 (3+2*r),Function.iterate_add_apply _ 3 (2*r),
    hfirst,hwv,hvu,hup']

theorem solution (n : ℕ) (hodd : n%2=1)
    (h : ∃ s r : ℕ, 0<s ∧ 0<r ∧ 2^r*(16*4^s)≤3^(r+2) ∧
      3^(r+3) ∣ 16*4^s*(3*n+1)-10) :
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k := by
  obtain ⟨s,r,hs,hr,hmargin,hdiv⟩ := h
  obtain ⟨k,hk,hkn,hm⟩ := collatz_coalescence_from_dyadic_relay n s r hodd hs hr hmargin hdiv
  exact ⟨k,2,2*r+2*s+8,hk,hkn,hm⟩
