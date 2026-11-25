-- Prove2me | solution 1 for collatz_two_run_exit_smaller_ancestor
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T18:32:00.516901+00:00
-- url     : https://prove2.me/submissions/781aed08-92b7-432f-9c4b-37e0491fd2a9

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq

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

/-- The two-run exit can have a smaller ancestor even when the exit itself
has not fallen below the original input. -/
theorem solution
    (L q H Q s r : ℕ) (hL : 4 ≤ L) (hq : 0 < q) (hQ : 0 < Q)
    (hbetween : 3^L*q+1 = 2^(H+1)*Q) (hs : 1 ≤ s) (hr : r ≤ H)
    (hdiv : 2^s ∣ 3^H*Q-1) (hres : 2^(s-1) % 3^r = 1)
    (hmargin : 2^r*(3^H*Q+2^(s-1)-1) ≤ 3^r*2^(s-1)*(2^L*q-1)) :
    ∃ k a b : ℕ, 0 < k ∧ k < 2^L*q-1 ∧
      collatzStep^[a] (2^L*q-1) = collatzStep^[b] k := by
  let P := 3^L*q
  let W := 3^H*Q
  let D := (2:ℕ)^(s-1)
  let n := 2^L*q-1
  have hDpos : 0 < D := Nat.two_pow_pos _
  have hBpos : 0 < (3:ℕ)^r := Nat.pow_pos (by decide)
  have h1lt : 1 < (3:ℕ)^r := hres ▸ Nat.mod_lt D hBpos
  have hrpos : 0 < r := by
    apply Nat.pos_of_ne_zero
    intro hzero
    simp [hzero] at h1lt
  have hnx : P+1=2*(2^H*Q) := by rw [hbetween,pow_succ]; ring
  have hgt : 1 < P := by
    have h3 : 3 ≤ 3^L := Nat.pow_le_pow_right (n := 3) (by decide) (by omega : 1 ≤ L)
    have hp : 3^L ≤ P := Nat.le_mul_of_pos_right _ hq
    omega
  have hW : 2^H*Q ≤ W := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) _)
  have hWpos : 1 < W := by omega
  have hfirst : collatzStep^[1+2*L] (2^L*q-1) = 2^H*Q-1 := by
    rw [Function.iterate_add_apply, trailingOnesRun L q hq, Function.iterate_one]
    change collatzStep (P-1) = 2^H*Q-1
    rw [stepEven _ (by omega)]
    omega
  obtain ⟨y,hy⟩ := hdiv
  change W-1 = 2^s*y at hy
  have hypos : 0 < y := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero,mul_zero] at hy
    omega
  have h2s : (2:ℕ)^s = 2*D := calc
    _ = 2^((s-1)+1) := by rw [show (s-1)+1 = s by omega]
    _ = _ := by rw [pow_succ]; dsimp [D]; ring
  have hid : D*(2*y+1) = W+(D-1) := by
    rw [h2s] at hy
    have hprod : (2*D)*y = D*(2*y) := by ring
    rw [hprod] at hy
    rw [Nat.mul_add, mul_one]
    omega
  have hWd : (3:ℕ)^r ∣ W := by
    refine ⟨3^(H-r)*Q, ?_⟩
    dsimp [W]
    conv_lhs => rw [show H = r+(H-r) by omega, pow_add]
    ring
  have hD1 : (D-1) % (3^r) = 0 := by
    have h1 : D-1+1 ≡ 0+1 [MOD 3^r] := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ D), zero_add]
      change D % (3^r) = 1 % (3^r)
      rw [Nat.mod_eq_of_lt h1lt]
      exact hres
    simpa [Nat.ModEq] using (Nat.ModEq.add_right_cancel' 1 h1)
  have hzd : (3:ℕ)^r ∣ 2*y+1 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    calc
      _ = (D*(2*y+1))%(3^r) := by
        rw [Nat.mul_mod, show D%(3^r)=1 from hres, one_mul, Nat.mod_mod]
      _ = (W+(D-1))%(3^r) := by rw [hid]
      _ = 0 := by rw [Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp hWd, hD1, zero_add, Nat.zero_mod]
  obtain ⟨u,hu⟩ := hzd
  have huPos : 0 < u := by
    apply Nat.pos_of_ne_zero
    intro zeroU
    rw [zeroU,mul_zero] at hu
    omega
  have hsmall : 2^r*u ≤ n := by
    have hmargin' : 2^r*(W+(D-1)) ≤ 3^r*D*n := by
      change 2^r*(W+D-1) ≤ 3^r*D*n at hmargin
      have heq : W+D-1 = W+(D-1) := by omega
      simpa only [heq] using hmargin
    have hscaled : 3^r*(D*(2^r*u)) ≤ 3^r*(D*n) := calc
      _ = 2^r*(D*(3^r*u)) := by ring
      _ = 2^r*(W+(D-1)) := by rw [← hu,hid]
      _ ≤ _ := hmargin'.trans_eq (Nat.mul_assoc _ _ _)
    exact Nat.le_of_mul_le_mul_left
      (Nat.le_of_mul_le_mul_left hscaled hBpos) hDpos
  have hkpos : 0 < 2^r*u-1 := by
    have ha : 2 ≤ 2^r := Nat.pow_le_pow_right (n := 2) (by decide) hrpos
    have hb : 2^r ≤ 2^r*u := Nat.le_mul_of_pos_right _ huPos
    omega
  refine ⟨2^r*u-1, s+(2*H+(1+2*L)), 1+2*r, hkpos, by omega, ?_⟩
  rw [Function.iterate_add_apply _ s _, Function.iterate_add_apply _ (2*H) (1+2*L),
    hfirst, trailingOnesRun H Q hQ, Function.iterate_add_apply _ 1 (2*r),
    trailingOnesRun r u huPos, ← hu]
  change collatzStep^[s] (W-1) = collatzStep^[1] (2*y+1-1)
  rw [hy,powerHalvings,Function.iterate_one,show 2*y+1-1 = 2*y by omega,
    stepEven _ (by omega)]
  omega
