-- Prove2me | solution 1 for collatz_smaller_merger_from_variable_halving_relay
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:13:13.936829+00:00
-- url     : https://prove2.me/submissions/2d0c1343-eb7f-44cd-8ec3-fcd664ac29f1

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

/-- Additive numerator of a sequence of ordinary odd steps with the
prescribed numbers of following halvings. The first exponent is first
in forward time. -/
private def collatzHalvingWordOffset : List ℕ → ℕ
  | [] => 0
  | e::w => 3^w.length+2^e*collatzHalvingWordOffset w

/-- The integer affine identity forces every intermediate division and
every parity required by a positive halving word. -/
private theorem collatz_halving_word_of_affine_identity
    (w : List ℕ) (x y : ℕ)
    (hword : ∀ e∈w, 0<e)
    (h : 3^w.length*x+collatzHalvingWordOffset w=2^w.sum*y) :
    collatzStep^[w.sum+w.length] x=y := by
  induction w generalizing x with
  | nil => simpa [collatzHalvingWordOffset] using h
  | cons e w ih =>
    have he : 0<e := hword e (List.mem_cons_self)
    have hcoef : 3^w.length*(3*x+1)+2^e*collatzHalvingWordOffset w =
        2^e*(2^w.sum*y) := calc
      _ = 3^(e::w).length*x+collatzHalvingWordOffset (e::w) := by
        simp only [List.length_cons,collatzHalvingWordOffset,pow_succ]
        ring
      _ = 2^(e::w).sum*y := h
      _ = _ := by rw [List.sum_cons,pow_add,Nat.mul_assoc]
    have hprod : 2^e ∣ 3^w.length*(3*x+1) :=
      (Nat.dvd_add_iff_left (Nat.dvd_mul_right _ _)).mpr ⟨_,hcoef⟩
    have hcop : (2^e).Coprime (3^w.length) :=
      ((by decide : Nat.Coprime 2 3).pow_left e).pow_right _
    obtain ⟨z,hz⟩ := hcop.dvd_of_dvd_mul_left hprod
    have hfirst : collatzStep^[e+1] x=z := oddStepThenHalves x z e he hz
    have hrest : 3^w.length*z+collatzHalvingWordOffset w=2^w.sum*y := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos e)
      calc
        _ = 3^w.length*(2^e*z)+2^e*collatzHalvingWordOffset w := by ring
        _ = _ := by rw [←hz]; exact hcoef
    have hend := ih z (fun a ha => hword a (List.mem_cons_of_mem _ ha)) hrest
    rw [show (e::w).sum+(e::w).length=(w.sum+w.length)+(e+1) by simp; omega,
      Function.iterate_add_apply,hfirst,hend]

/-- The previous relay is the case where both interior halving counts
are two. Here each halving count can be chosen independently. -/
private theorem collatz_coalescence_from_variable_halving_relay (n s r a b : ℕ)
    (hodd : n%2=1) (hr : 0<r) (ha : 2≤a) (hb : 2≤b)
    (hmargin : 2^r*(2^(a+b)*4^s)≤3^(r+2))
    (hdiv : 3^(r+3) ∣ 2^(a+b)*4^s*(3*n+1)+18-(2^(a+b)+3*2^b)) :
    ∃ k : ℕ, 0<k ∧ k<n ∧ collatzStep^[2] n=collatzStep^[2*r+a+b+2*s+4] k := by
  let P := 2^(a+b)*4^s
  let D := 2^(a+b)+3*2^b
  let word : List ℕ := [b,a,2*s+1]
  let p := (3*n+1)/2
  have hpn : 3*n+1=2*p := by dsimp [p]; omega
  have h2a : 4≤2^a := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) ha
  have h2b : 4≤2^b := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hb
  have h2ab : 16≤2^(a+b) := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega : 4≤a+b)
  have hDb : 18≤D := by dsimp [D]; omega
  have hDupper : D≤2*P := calc
    _ = 2^(a+b)+3*2^b := rfl
    _ ≤ 2^(a+b)+2^(a+b) := by
      rw [pow_add]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    _ = 2*(2^(a+b)) := by omega
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide)))
  have hposNumerator : D<P*(3*n+1)+18 := by
    have hmain := Nat.mul_le_mul_left P (by omega : 2≤3*n+1)
    rw [Nat.mul_comm P 2] at hmain
    omega
  obtain ⟨z,hz⟩ := hdiv
  change P*(3*n+1)+18-D=3^(r+3)*z at hz
  have hzpos : 0<z := by
    by_contra! hzero
    rw [Nat.eq_zero_of_le_zero hzero,mul_zero] at hz
    omega
  have hformula : 3^(r+3)*z + D=P*(3*n+1)+18 := by omega
  have hmul : 3^(r+3)*z=27*(3^r*z) := by rw [pow_add]; norm_num; ring
  have hword : ∀ e∈word, 0<e := by
    intro e he
    simp [word] at he
    omega
  have hclock : word.sum+word.length=a+b+2*s+4 := by simp [word]; omega
  have hoffset : collatzHalvingWordOffset word=9+D := by
    simp [word,collatzHalvingWordOffset,D,pow_add]
    ring
  have htarget : 2^word.sum*p=P*(3*n+1) := by
    have hlen : word.sum=(a+b)+2*s+1 := by simp [word]; omega
    rw [hlen,pow_succ,pow_add,pow_mul,hpn]
    change (2^(a+b)*4^s)*2*p=P*(2*p)
    dsimp [P]
    ring
  let w := 3^r*z-1
  have hbeta : 3^word.length*w+collatzHalvingWordOffset word=2^word.sum*p := by
    rw [hoffset,htarget]
    change 27*(3^r*z-1)+(9+D)=P*(3*n+1)
    have h3z : 0<3^r*z := Nat.mul_pos (Nat.pow_pos (by decide)) hzpos
    omega
  have hlast := collatz_halving_word_of_affine_identity word w p hword hbeta
  rw [hclock] at hlast
  have hbound : 3^(r+3)*(2^r*z)<3^(r+3)*(n+1) := calc
    _ = 2^r*(3^(r+3)*z) := by ring
    _ ≤ 2^r*(P*(3*n+1)) := Nat.mul_le_mul_left _ (by omega)
    _ = (2^r*P)*(3*n+1) := by ring
    _ ≤ 3^(r+2)*(3*n+1) := Nat.mul_le_mul_right _ hmargin
    _ < _ := by
      have hfold : (3:ℕ)^(r+3)=3^(r+2)*3 := by
        rw [show r+3=(r+2)+1 by omega,pow_succ]
      rw [hfold,Nat.mul_assoc]
      exact Nat.mul_lt_mul_of_pos_left (by omega : 3*n+1<3*(n+1))
        (Nat.pow_pos (by decide : 0<(3:ℕ)))
  have hsmall : 2^r*z<n+1 :=
    (Nat.mul_lt_mul_left (Nat.pow_pos (by decide : 0<(3:ℕ)))).mp hbound
  let k := 2^r*z-1
  have hk : 0<k := by
    have h2r : 2≤2^r := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega : 1≤r)
    have h2z : 2^r≤2^r*z := Nat.le_mul_of_pos_right _ hzpos
    dsimp [k]
    omega
  have hlt : k<n := by dsimp [k]; omega
  have hfirst : collatzStep^[2*r] k=w := trailingOnesRun r z hzpos
  have hstart : collatzStep^[2] n=p := oddStepThenHalves n p 1 (by decide) (by simpa using hpn)
  refine ⟨k,hk,hlt,?_⟩
  rw [hstart,show 2*r+a+b+2*s+4=(a+b+2*s+4)+2*r by omega,
    Function.iterate_add_apply,hfirst,hlast]

theorem solution (n : ℕ) (hodd : n%2=1)
    (h : ∃ s r a b : ℕ, 0<r ∧ 2≤a ∧ 2≤b ∧
      2^r*(2^(a+b)*4^s)≤3^(r+2) ∧
      3^(r+3) ∣ 2^(a+b)*4^s*(3*n+1)+18-(2^(a+b)+3*2^b)) :
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k := by
  obtain ⟨s,r,a,b,hr,ha,hb,hmargin,hdiv⟩ := h
  obtain ⟨k,hk,hkn,hm⟩ := collatz_coalescence_from_variable_halving_relay n s r a b hodd
    hr ha hb hmargin hdiv
  exact ⟨k,2,2*r+a+b+2*s+4,hk,hkn,hm⟩
