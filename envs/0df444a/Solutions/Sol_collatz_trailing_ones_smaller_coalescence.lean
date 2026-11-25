-- Prove2me | solution 1 for collatz_trailing_ones_smaller_coalescence
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T18:12:30.156262+00:00
-- url     : https://prove2.me/submissions/1a09dd3e-c025-47ff-a0a3-870163172ee8

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

/- Progression verifier adapted from immiq's Prove2Me submission
   1843fe6d-cde2-4133-a4d5-fcfa32356e48 (Apache-2.0).
   Track the image of an entire arithmetic progression. An even coefficient
   makes parity independent of the parameter. -/
private def traceProgression : ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | 0, a, b => some (a, b)
  | t + 1, a, b =>
    if a % 2 = 0 then
      if b % 2 = 0 then traceProgression t (a / 2) (b / 2)
      else traceProgression t (3 * a) (3 * b + 1)
    else none

private theorem traceProgression_sound (t a b u v : ℕ)
    (h : traceProgression t a b = some (u, v)) (q : ℕ) :
    collatzStep^[t] (a * q + b) = u * q + v := by
  induction t generalizing a b with
  | zero =>
    simp [traceProgression] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | succ t ih =>
    simp only [traceProgression] at h
    split at h
    · rename_i ha
      have ha' : a = 2 * (a / 2) := by omega
      rw [Function.iterate_succ_apply]
      split at h
      · rename_i hb
        have hb' : b = 2 * (b / 2) := by omega
        have hx : a * q + b = 2 * ((a / 2) * q + b / 2) := by
          calc
            a * q + b = (2 * (a / 2)) * q + 2 * (b / 2) := congrArg₂ (· + ·) (congrArg (· * q) ha') hb'
            _ = _ := by ring
        rw [hx]
        simpa [collatzStep] using ih _ _ h
      · rename_i hb
        have hb' : b = 2 * (b / 2) + 1 := by omega
        have hx : a * q + b = 2 * ((a / 2) * q + b / 2) + 1 := by
          calc
            a * q + b = (2 * (a / 2)) * q + (2 * (b / 2) + 1) := congrArg₂ (· + ·) (congrArg (· * q) ha') hb'
            _ = _ := by ring
        have hodd : ¬ Even (a * q + b) := by simp [hx]
        rw [collatzStep, if_neg hodd]
        convert ih _ _ h using 2
        ring
    · contradiction

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

private theorem doubleStepAfterRun (P : ℕ) (h : P % 4 = 3) :
    collatzStep^[2] (P-1) = (3*P-1)/2 := by
  have he : (P-1)%2 = 0 := by omega
  have ho : ((P-1)/2)%2 = 1 := by omega
  rw [Function.iterate_succ_apply, Function.iterate_one, stepEven _ he, stepOdd _ ho]
  omega

private theorem compatibleRun (L q : ℕ) (hL : 4 ≤ L) (hq : 0 < q)
    (h : (3^L*q) % 4 = 1) :
    ∃ k a b : ℕ, 0 < k ∧ k < 2^L*q-1 ∧
      collatzStep^[a] (2^L*q-1) = collatzStep^[b] k := by
  let P := 3^(L-2)*q
  have h1 : 3^L*q = 9*P := calc
    _ = 3^((L-2)+2)*q := by rw [show (L-2)+2 = L by omega]
    _ = _ := by rw [pow_add]; dsimp [P]; ring
  have h2 : 3^(L-2)*(3*q) = 3*P := by dsimp [P]; ring
  have hpow : 2^L*q = 4*(2^(L-2)*q) := by
    calc
      2^L*q = 2^((L-2)+2)*q := by rw [show (L-2)+2 = L by omega]
      _ = _ := by rw [pow_add]; ring
  have hkpow : 2^(L-2)*(3*q) = 3*(2^(L-2)*q) := by ring
  have hkpos : 0 < 2^(L-2)*q := Nat.mul_pos (Nat.two_pow_pos _) hq
  have hsmall : (3*P) % 4 = 3 := by rw [h1] at h; omega
  refine ⟨2^(L-2)*(3*q)-1, 1+2*L, 2+2*(L-2), by omega, by omega, ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_add_apply, trailingOnesRun L q hq,
    trailingOnesRun (L-2) (3*q) (by omega), h1, h2, Function.iterate_one,
    stepEven (9*P-1) (by rw [h1] at h; omega), doubleStepAfterRun _ hsmall]
  congr 1
  omega

private theorem checkedRow (L q M r s a b u v inverse : ℕ)
    (hL : 4 ≤ L) (hq : 0 < q) (hmod : (3^L*q) % M = r)
    (hres : (9*s) % M = r) (hinv : (inverse*9) % M = 1) (hs : s < M) (hspos : 0 < s)
    (ha : traceProgression a (9*M) (9*s-1) = some (u,v))
    (hb : traceProgression b M (s-1) = some (u,v)) :
    ∃ k i j : ℕ, 0 < k ∧ k < 2^L*q-1 ∧
      collatzStep^[i] (2^L*q-1) = collatzStep^[j] k := by
  let X := 3^(L-2)*q
  have hp : 3^L*q = 9*X := calc
    _ = 3^((L-2)+2)*q := by rw [show (L-2)+2 = L by omega]
    _ = _ := by rw [pow_add]; dsimp [X]; ring
  have hXX : (9*X) % M = (9*s) % M := by rw [← hp, hmod, hres]
  have cancelNine (x : ℕ) : ((inverse*9)*x) % M = x % M := by
    rw [Nat.mul_mod, hinv, one_mul, Nat.mod_mod]
  have hX : X % M = s := calc
    X % M = ((inverse*9)*X) % M := (cancelNine X).symm
    _ = ((inverse*9)*s) % M := by
      rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_mod inverse (9*X), Nat.mul_mod inverse (9*s), hXX]
    _ = s := by rw [cancelNine, Nat.mod_eq_of_lt hs]
  let j := X/M
  have hquot : X = M*j+s := by
    simpa only [j, hX] using (Nat.mod_add_div X M).symm.trans (Nat.add_comm _ _)
  have hxlo : X-1 = M*j+(s-1) := by rw [hquot]; omega
  have hxhi : 9*X-1 = (9*M)*j+(9*s-1) := by
    have heq : 9*X = (9*M)*j+9*s := by rw [hquot]; ring
    omega
  have hpow : 2^L*q = 4*(2^(L-2)*q) := calc
    _ = 2^((L-2)+2)*q := by rw [show (L-2)+2 = L by omega]
    _ = _ := by rw [pow_add]; ring
  have hkpos : 2 ≤ 2^(L-2)*q := calc
    2 ≤ 2^(L-2) := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ L-2 by omega)
    _ ≤ _ := Nat.le_mul_of_pos_right _ hq
  refine ⟨2^(L-2)*q-1, a+2*L, b+2*(L-2), by omega, by omega, ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_add_apply, trailingOnesRun L q hq,
    trailingOnesRun (L-2) q hq, hp, hxhi]
  change collatzStep^[a] ((9*M)*j+(9*s-1)) = collatzStep^[b] (X-1)
  rw [hxlo, traceProgression_sound _ _ _ _ _ ha, traceProgression_sound _ _ _ _ _ hb]

private theorem longExit (L q : ℕ) (hq : 0 < q)
    (h : let P := 3^L*q
      P % 4 = 3 ∧ ∃ s : ℕ, 2 ≤ s ∧ 2^s ∣ 3*P-1 ∧ 3*3^L+2^s ≤ 2^(L+s)) :
    ∃ k a b : ℕ, 0 < k ∧ k < 2^L*q-1 ∧
      collatzStep^[a] (2^L*q-1) = collatzStep^[b] k := by
  let P := 3^L*q
  rcases h with ⟨hmod, s, hs, ⟨k,hdiv⟩, hgain⟩
  change P % 4 = 3 at hmod
  change 3*P-1 = 2^s*k at hdiv
  have hp : 0 < P := Nat.mul_pos (Nat.pow_pos (by decide)) hq
  have hk : 0 < k := by
    by_contra! hh
    have hz : k = 0 := by omega
    rw [hz, mul_zero] at hdiv
    omega
  let n := 2^L*q-1
  have hn : n+1 = 2^L*q := by
    have := Nat.mul_pos (Nat.two_pow_pos L) hq
    dsimp [n]
    omega
  have hsum : 3*P+2^s ≤ 2^s*(n+1) := calc
    _ ≤ (3*3^L+2^s)*q := by
      have hx : 2^s ≤ 2^s*q := Nat.le_mul_of_pos_right _ hq
      dsimp [P]
      rw [Nat.add_mul, Nat.mul_assoc]
      omega
    _ ≤ 2^(L+s)*q := Nat.mul_le_mul_right q hgain
    _ = _ := by rw [hn, pow_add]; ring
  have hsm : k < n := (Nat.mul_lt_mul_left (Nat.two_pow_pos s)).mp (by
    rw [← hdiv]
    rw [Nat.mul_add, mul_one] at hsum
    omega)
  have hd : (3*P-1)/2 = 2^(s-1)*k := by
    rw [hdiv]
    have hdbl : 2^s = 2 * 2^(s-1) := calc
      _ = 2^((s-1)+1) := by rw [show (s-1)+1 = s by omega]
      _ = _ := by rw [pow_succ]; ring
    rw [hdbl, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
  refine ⟨k, (s-1)+(2+2*L), 0, hk, hsm, ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_add_apply, trailingOnesRun L q hq]
  change collatzStep^[s-1] (collatzStep^[2] (P-1)) = k
  rw [doubleStepAfterRun _ hmod, hd, powerHalvings]


theorem solution (L q : ℕ) (hL : 4 ≤ L) (hq : 0 < q)
    (hcase : let P := 3^L * q
      P % 4 = 1 ∨
      P % 256 ∈ ([43] : List ℕ) ∨
      P % 512 ∈ ([199, 363] : List ℕ) ∨
      P % 1024 ∈ ([235, 395, 583] : List ℕ) ∨
      P % 2048 ∈ ([263, 795, 839, 1163, 1175, 1515] : List ℕ) ∨
      P % 4096 ∈ ([523, 631, 775, 1003, 1675, 1687, 1895, 2331, 2351, 2375] : List ℕ) ∨
      P % 8192 ∈ ([1051, 1263, 1547, 3079, 3355, 3375, 3399, 3787, 3847, 3991, 4699, 4747, 4759, 5207, 6123, 7015, 7799] : List ℕ) ∨
      (P % 4 = 3 ∧ ∃ s : ℕ, 2 ≤ s ∧ 2^s ∣ 3*P-1 ∧ 3*3^L+2^s ≤ 2^(L+s))) :
    ∃ k a b : ℕ, 0 < k ∧ k < 2^L*q-1 ∧
      collatzStep^[a] (2^L*q-1) = collatzStep^[b] k := by
  rcases hcase with h4 | h256 | h512 | h1024 | h2048 | h4096 | h8192 | hlargeExit
  · exact compatibleRun L q hL hq h4
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h256
    exact checkedRow L q 256 43 147 10 12 81 47 57 hL hq h256 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h512
    rcases h512 with hr199 | hr363
    · exact checkedRow L q 512 199 79 12 14 243 38 57 hL hq hr199 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 512 363 211 12 14 243 101 57 hL hq hr363 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1024
    rcases h1024 with hr235 | hr395 | hr583
    · exact checkedRow L q 1024 235 595 14 16 729 425 569 hL hq hr235 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 1024 395 499 13 15 243 119 569 hL hq hr395 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 1024 583 975 14 16 729 695 569 hL hq hr583 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2048
    rcases h2048 with hr263 | hr795 | hr839 | hr1163 | hr1175 | hr1515
    · exact checkedRow L q 2048 263 1167 15 17 729 416 1593 hL hq hr263 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 2048 795 771 14 16 243 92 1593 hL hq hr795 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 2048 839 1231 16 18 2187 1316 1593 hL hq hr839 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 2048 1163 1267 15 17 729 452 1593 hL hq hr1163 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 2048 1175 1951 15 17 729 695 1593 hL hq hr1175 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 2048 1515 851 16 18 2187 911 1593 hL hq hr1515 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h4096
    rcases h4096 with hr523 | hr631 | hr775 | hr1003 | hr1675 | hr1687 | hr1895 | hr2331 | hr2351 | hr2375
    · exact checkedRow L q 4096 523 3699 16 18 729 659 3641 hL hq hr523 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 4096 631 3711 17 19 2187 1982 3641 hL hq hr631 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 4096 775 3727 17 19 2187 1991 3641 hL hq hr775 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 4096 1003 2387 18 20 6561 3827 3641 hL hq hr1003 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 4096 1675 3827 17 19 2187 2045 3641 hL hq hr1675 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 4096 1687 2463 17 19 2187 1316 3641 hL hq hr1687 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 4096 1895 2031 16 18 729 362 3641 hL hq hr1895 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 4096 2331 259 16 18 729 47 3641 hL hq hr2331 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 4096 2351 3447 16 18 729 614 3641 hL hq hr2351 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 4096 2375 719 18 20 6561 1154 3641 hL hq hr2375 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h8192
    rcases h8192 with hr1051 | hr1263 | hr1547 | hr3079 | hr3355 | hr3375 | hr3399 | hr3787 | hr3847 | hr3991 | hr4699 | hr4747 | hr4759 | hr5207 | hr6123 | hr7015 | hr7799
    · exact checkedRow L q 8192 1051 1027 17 19 729 92 3641 hL hq hr1051 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 1263 2871 18 20 2187 767 3641 hL hq hr1263 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 1547 4723 18 20 2187 1262 3641 hL hq hr1547 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 3079 3983 18 20 2187 1064 3641 hL hq hr3079 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 3355 1283 18 20 2187 344 3641 hL hq hr3355 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 3375 375 18 20 2187 101 3641 hL hq hr3375 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 3399 5839 20 22 19683 14033 3641 hL hq hr3399 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 3787 1331 17 19 729 119 3641 hL hq hr3787 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 3847 6799 19 21 6561 5447 3641 hL hq hr3847 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 3991 6815 18 20 2187 1820 3641 hL hq hr3991 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 4699 4163 17 19 729 371 3641 hL hq hr4699 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 4747 6899 19 21 6561 5528 3641 hL hq hr4747 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 4759 1439 19 21 6561 1154 3641 hL hq hr4759 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 5207 2399 18 20 2187 641 3641 hL hq hr5207 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 6123 3411 20 22 19683 8201 3641 hL hq hr6123 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 7015 7151 18 20 2187 1910 3641 hL hq hr7015 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact checkedRow L q 8192 7799 2687 19 21 6561 2153 3641 hL hq hr7799 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact longExit L q hq hlargeExit
