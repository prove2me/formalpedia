-- Prove2me | solution 1 for collatz_coalescence_at_arbitrary_odd_run_exit
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T18:40:33.240069+00:00
-- url     : https://prove2.me/submissions/436c93ee-7fe6-4950-8b4f-74e3844a158d

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

private def oddRunEnd (x : ℕ) : ℕ :=
  let r := (x+1).factorization 2
  3^r*((x+1)/2^r)-1

private def oddRunJump (x : ℕ) : ℕ :=
  let w := oddRunEnd x
  w/2^(w.factorization 2)

private theorem stepPos (x : ℕ) (hx : 0 < x) : 0 < collatzStep x := by
  unfold collatzStep
  split
  · rename_i he
    have hm := Nat.even_iff.mp he
    omega
  · omega

private theorem iteratePos (t x : ℕ) (hx : 0 < x) : 0 < collatzStep^[t] x := by
  induction t with
  | zero => exact hx
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact stepPos _ ih

private theorem runEnd_reachable (x : ℕ) :
    ∃ t : ℕ, collatzStep^[t] x = oddRunEnd x := by
  let r := (x+1).factorization 2
  let q := (x+1)/2^r
  have hf : 2^r*q = x+1 := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hq : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz,mul_zero] at hf
    exact (Nat.succ_ne_zero x) hf.symm
  have hm := trailingOnesRun r q hq
  rw [hf, Nat.add_sub_cancel] at hm
  exact ⟨2*r, hm⟩

private theorem halving_reachable (x s : ℕ) (hd : 2^s ∣ x) :
    collatzStep^[s] x = x/2^s := by
  have hf : 2^s*(x/2^s)=x := by simpa [Nat.mul_comm] using Nat.div_mul_cancel hd
  have hm := powerHalvings s (x/2^s)
  nth_rw 1 [hf] at hm
  exact hm

private theorem jump_reachable (x : ℕ) :
    ∃ t : ℕ, collatzStep^[t] x = oddRunJump x := by
  obtain ⟨t,ht⟩ := runEnd_reachable x
  let w := oddRunEnd x
  let s := w.factorization 2
  have hd : 2^s ∣ w := ⟨w/2^s, (Nat.ordProj_mul_ordCompl_eq_self _ _).symm⟩
  refine ⟨s+t, ?_⟩
  rw [Function.iterate_add_apply _ s t,ht]
  exact halving_reachable w s hd

private theorem jumpIter_reachable (j n : ℕ) :
    ∃ t : ℕ, collatzStep^[t] n = oddRunJump^[j] n := by
  induction j with
  | zero => exact ⟨0,rfl⟩
  | succ j ih =>
    obtain ⟨t,ht⟩ := ih
    obtain ⟨s,hs⟩ := jump_reachable (oddRunJump^[j] n)
    refine ⟨s+t, ?_⟩
    rw [Function.iterate_add_apply _ s t,ht,Function.iterate_succ_apply']
    exact hs

private theorem oddRunAncestor (y e : ℕ) (hy : 0 < y) :
    let z := 2^e*y+1
    let r := z.factorization 3
    let u := z/3^r
    let k := 2^r*u-1
    0 < k ∧ collatzStep^[e+2*r] k = y := by
  intro z r u k
  have hz : 2 ≤ z := by
    have hp : 0 < 2^e*y := Nat.mul_pos (Nat.two_pow_pos _) hy
    dsimp [z]
    omega
  have hfactor : 3^r*u = z := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hu : 0 < u := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero,mul_zero] at hfactor
    omega
  have hk : 0 < k := by
    dsimp only [k]
    by_cases hr : r = 0
    · rw [hr,pow_zero,one_mul] at hfactor ⊢
      omega
    · have htwo : 2 ≤ 2^r :=
        Nat.pow_le_pow_right (n := 2) (by decide) (Nat.pos_of_ne_zero hr)
      have hle : 2^r ≤ 2^r*u := Nat.le_mul_of_pos_right _ hu
      omega
  refine ⟨hk, ?_⟩
  dsimp only [k]
  rw [Function.iterate_add_apply _ e (2*r), trailingOnesRun r u hu,hfactor]
  have heq : z-1 = 2^e*y := by dsimp [z]
  rw [heq,powerHalvings]

theorem solution (n : ℕ) (hn : 0 < n)
    (h : let runEnd : ℕ → ℕ := fun x =>
        let r := (x+1).factorization 2
        3^r*((x+1)/2^r)-1
      let jump : ℕ → ℕ := fun x =>
        let w := runEnd x
        w/2^(w.factorization 2)
      ∃ j s e : ℕ,
        let w := runEnd (jump^[j] n)
        let y := w/2^s
        let z := 2^e*y+1
        let r := z.factorization 3
        2^s ∣ w ∧ (y < n ∨ 2^r*(z/3^r)-1 < n)) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  change (∃ j s e : ℕ,
    let w := oddRunEnd (oddRunJump^[j] n)
    let y := w/2^s
    let z := 2^e*y+1
    let r := z.factorization 3
    2^s ∣ w ∧ (y<n ∨ 2^r*(z/3^r)-1<n)) at h
  obtain ⟨j,s,e,hd,hsmall⟩ := h
  let x := oddRunJump^[j] n
  let w := oddRunEnd x
  let y := w/2^s
  let z := 2^e*y+1
  let r := z.factorization 3
  let k := 2^r*(z/3^r)-1
  change 2^s ∣ w at hd
  change y<n ∨ k<n at hsmall
  obtain ⟨t,ht⟩ := jumpIter_reachable j n
  obtain ⟨b,hb⟩ := runEnd_reachable x
  have hprefix : collatzStep^[s+(b+t)] n = y := by
    rw [Function.iterate_add_apply _ s (b+t), Function.iterate_add_apply _ b t, ht]
    change collatzStep^[s] (collatzStep^[b] x) = y
    rw [hb]
    exact halving_reachable w s hd
  have hy : 0 < y := hprefix ▸ iteratePos _ n hn
  rcases hsmall with h | h
  · exact ⟨y,s+(b+t),0,hy,h,hprefix⟩
  · obtain ⟨hk,heq⟩ := oddRunAncestor y e hy
    exact ⟨k,s+(b+t),e+2*r,hk,h,hprefix.trans heq.symm⟩
