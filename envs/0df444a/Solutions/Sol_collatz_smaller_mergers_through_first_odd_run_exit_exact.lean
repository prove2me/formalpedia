-- Prove2me | solution 1 for collatz_smaller_mergers_through_first_odd_run_exit_exact
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:40:15.192082+00:00
-- url     : https://prove2.me/submissions/96e6beba-6f49-47ff-9f33-8f413e940b3e

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring

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

private def phaseEnd (x : ℕ) : ℕ :=
  let r := (x+1).factorization 2
  3^r*((x+1)/2^r)-1

private def phaseJump (x : ℕ) : ℕ :=
  let w := phaseEnd x
  w/2^(w.factorization 2)

private theorem ordinaryStepPositive (x : ℕ) (hx : 0<x) : 0 < collatzStep x := by
  unfold collatzStep
  split
  · rename_i he
    have hm := Nat.even_iff.mp he
    omega
  · omega

private theorem ordinaryIteratePositive (t x : ℕ) (hx : 0<x) :
    0 < collatzStep^[t] x := by
  induction t with
  | zero => exact hx
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact ordinaryStepPositive _ ih

private def phaseDuration (x : ℕ) : ℕ :=
  (phaseEnd x).factorization 2 + 2*((x+1).factorization 2)

private theorem phaseJumpProgressExact (x : ℕ) (hx : 0<x) :
    0<phaseDuration x ∧ collatzStep^[phaseDuration x] x=phaseJump x ∧
      phaseJump x%2=1 := by
  let r := (x+1).factorization 2
  let q := (x+1)/2^r
  let w := phaseEnd x
  let s := w.factorization 2
  have hsplit : 2^r*q=x+1 := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hq : 0<q := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero,mul_zero] at hsplit
    exact (Nat.succ_ne_zero x) hsplit.symm
  have hend := trailingOnesRun r q hq
  rw [hsplit,Nat.add_sub_cancel] at hend
  change collatzStep^[2*r] x=w at hend
  have hw : 0<w := hend ▸ ordinaryIteratePositive _ x hx
  have he : 2^s*(w/2^s)=w := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hjumpOdd : phaseJump x%2=1 := by
    have hn : ¬ 2 ∣ w/2^s := Nat.not_dvd_ordCompl Nat.prime_two (Nat.ne_of_gt hw)
    rw [Nat.dvd_iff_mod_eq_zero] at hn
    change w/2^s%2=1
    omega
  have hjump : collatzStep^[s+2*r] x=phaseJump x := by
    rw [Function.iterate_add_apply _ s (2*r),hend]
    have hh := powerHalvings s (w/2^s)
    nth_rw 1 [he] at hh
    exact hh
  have ht : 0<s+2*r := by
    by_contra! hn
    have hr : r=0 := by omega
    have hs : s=0 := by omega
    have hqOdd : q%2=1 := by
      have hn2 : ¬2 ∣ q := Nat.not_dvd_ordCompl Nat.prime_two (Nat.succ_ne_zero x)
      rw [Nat.dvd_iff_mod_eq_zero] at hn2
      omega
    have hxe : x%2=0 := by rw [hr,pow_zero,one_mul] at hsplit; omega
    rw [hs,hr,mul_zero,add_zero] at hjump
    have hh : x=phaseJump x := hjump
    rw [← hh,hxe] at hjumpOdd
    contradiction
  exact ⟨ht,hjump,hjumpOdd⟩

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

/-- The pair of length and affine offset can be evaluated with an
ordinary list fold. -/
private theorem collatz_halving_word_offset_fold (w : List ℕ) :
    w.foldr (fun e (p : ℕ × ℕ) => (p.1+1,3^p.1+2^e*p.2)) (0,0) =
      (w.length,collatzHalvingWordOffset w) := by
  induction w with
  | nil => rfl
  | cons e w ih => simp [collatzHalvingWordOffset,ih]

private theorem oddTarget_halving_word (t x y : ℕ) (hy : y%2=1)
    (h : collatzStep^[t] x=y) :
    ∃ (s u : ℕ) (w : List ℕ), x=2^s*u ∧ u%2=1 ∧
      (∀ a∈w, 0<a) ∧ t=s+(w.sum+w.length) ∧
      3^w.length*u+collatzHalvingWordOffset w=2^w.sum*y := by
  induction t generalizing x with
  | zero =>
    change x=y at h
    subst x
    exact ⟨0,y,[],by simp,hy,by simp,by simp,by simp [collatzHalvingWordOffset]⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply] at h
    obtain ⟨s,u,w,hstart,hu,hword,ht,hend⟩ := ih _ h
    by_cases he : x%2=0
    · rw [stepEven _ he] at hstart
      have hx : x=2^(s+1)*u := calc
        _ = 2*(x/2) := by omega
        _ = _ := by rw [hstart,pow_succ]; ring
      exact ⟨s+1,u,w,hx,hu,hword,by omega,hend⟩
    · have ho : x%2=1 := by omega
      rw [stepOdd _ ho] at hstart
      have hs : 0<s := by
        by_contra! hzero
        rw [Nat.eq_zero_of_le_zero hzero,pow_zero,one_mul] at hstart
        omega
      refine ⟨0,x,s::w,by simp,ho,?_,?_,?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact hs
        · exact hword a ha'
      · simp only [zero_add,List.length_cons,List.sum_cons]
        omega
      · calc
          3^(s::w).length*x+collatzHalvingWordOffset (s::w) =
              3^w.length*(3*x+1)+2^s*collatzHalvingWordOffset w := by
            simp only [List.length_cons,pow_succ,collatzHalvingWordOffset]
            ring
          _ = 2^s*(3^w.length*u+collatzHalvingWordOffset w) := by
            rw [hstart]
            ring
          _ = 2^(s::w).sum*y := by rw [hend,List.sum_cons,pow_add,Nat.mul_assoc]

/-- Visiting an odd target from a positive start below the bound is
equivalent to the affine conditions on a finite word of halving counts. -/
private theorem collatz_odd_target_smaller_visitor_iff_word (n y : ℕ) (hy : y%2=1) :
    (∃ k t : ℕ, 0<k ∧ k<n ∧ collatzStep^[t] k=y) ↔
      ∃ w : List ℕ, (∀ a∈w, 0<a) ∧
        let B := collatzHalvingWordOffset w
        let z := 2^w.sum*y-B
        0<z ∧ 3^w.length ∣ z ∧ z<3^w.length*n := by
  constructor
  · rintro ⟨k,t,hk,hl,hkt⟩
    obtain ⟨s,u,w,hstart,hu,hword,_,hend⟩ := oddTarget_halving_word t k y hy hkt
    have hu0 : 0<u := by omega
    have hlu : u<n := (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos s)).trans_lt (hstart ▸ hl)
    have hz : 2^w.sum*y-collatzHalvingWordOffset w=3^w.length*u := by omega
    refine ⟨w,hword,?_⟩
    dsimp only
    rw [hz]
    have hp : 0<(3:ℕ)^w.length := Nat.pow_pos (by decide)
    exact ⟨Nat.mul_pos hp hu0,⟨u,rfl⟩,Nat.mul_lt_mul_of_pos_left hlu hp⟩
  · rintro ⟨w,hword,hdata⟩
    let z := 2^w.sum*y-collatzHalvingWordOffset w
    change 0<z ∧ 3^w.length ∣ z ∧ z<3^w.length*n at hdata
    obtain ⟨hz,⟨k,hfac⟩,hlt⟩ := hdata
    have hk : 0<k := by
      by_contra! he
      rw [Nat.eq_zero_of_le_zero he,mul_zero] at hfac
      omega
    have hkn : k<n := (Nat.mul_lt_mul_left (Nat.pow_pos (by decide : 0<(3:ℕ)))).mp
      (by rwa [hfac] at hlt)
    have ha : 3^w.length*k+collatzHalvingWordOffset w=2^w.sum*y := by dsimp [z] at *; omega
    exact ⟨k,w.sum+w.length,hk,hkn,collatz_halving_word_of_affine_identity w k y hword ha⟩

/-- The first odd-run endpoint includes the halvings after the last odd
step. Its smaller visitors have an exact affine-word characterization. -/
private theorem collatz_first_run_exit_smaller_visitor_iff_word (n : ℕ) (hn : 0<n) :
    (∃ k t : ℕ, 0<k ∧ k<n ∧ collatzStep^[t] k=collatzStep^[phaseDuration n] n) ↔
      ∃ w : List ℕ, (∀ a∈w, 0<a) ∧
        let y := phaseJump n
        let B := collatzHalvingWordOffset w
        let z := 2^w.sum*y-B
        0<z ∧ 3^w.length ∣ z ∧ z<3^w.length*n := by
  have ⟨_,heq,hodd⟩ := phaseJumpProgressExact n hn
  rw [heq]
  exact collatz_odd_target_smaller_visitor_iff_word n _ hodd

/-- Any merger through the end of the first run gives a visitor to its
odd endpoint, regardless of how far the smaller start travels. -/
private theorem collatz_first_run_exit_word_iff_early_merger (n : ℕ) (hn : 0<n) :
    (∃ k a b : ℕ, 0<k ∧ k<n ∧ a≤phaseDuration n ∧ collatzStep^[a] n=collatzStep^[b] k) ↔
      ∃ w : List ℕ, (∀ a∈w, 0<a) ∧
        let y := phaseJump n
        let B := collatzHalvingWordOffset w
        let z := 2^w.sum*y-B
        0<z ∧ 3^w.length ∣ z ∧ z<3^w.length*n := by
  rw [←collatz_first_run_exit_smaller_visitor_iff_word n hn]
  constructor
  · rintro ⟨k,a,b,hk,hkn,ha,h⟩
    refine ⟨k,(phaseDuration n-a)+b,hk,hkn,?_⟩
    rw [Function.iterate_add_apply,←h,←Function.iterate_add_apply]
    rw [show (phaseDuration n-a)+a=phaseDuration n by omega]
  · rintro ⟨k,t,hk,hkn,he⟩
    exact ⟨k,phaseDuration n,t,hk,hkn,le_rfl,he.symm⟩

theorem solution (n : ℕ) (hn : 0<n) :
    let r := (n+1).factorization 2
    let w := 3^r*((n+1)/2^r)-1
    let s := w.factorization 2
    (∃ k a b : ℕ, 0<k ∧ k<n ∧ a≤s+2*r ∧ collatzStep^[a] n=collatzStep^[b] k) ↔
    (∃ v : List ℕ, (∀ a∈v, 0<a) ∧
      let B := (v.foldr (fun a (p : ℕ × ℕ) => (p.1+1,3^p.1+2^a*p.2)) (0,0)).2
      let z := 2^v.sum*(w/2^s)-B
      0<z ∧ 3^v.length ∣ z ∧ z<3^v.length*n) := by
  simpa only [collatz_halving_word_offset_fold,phaseDuration,phaseEnd,phaseJump] using
    collatz_first_run_exit_word_iff_early_merger n hn
