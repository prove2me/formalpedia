-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P66.separatingF_submodular
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-20T21:17:05.963513+00:00
-- url     : https://prove2.me/submissions/402aab5b-6c7b-4a02-8976-bf7a41d44016

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P66
noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P66

open scoped BigOperators

open QAlgorithms (IsDensityMatrix vnEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

def AuxSF_G (n : ℕ) (K : Finset (Fin 3)) (j : ℕ) : ℝ :=
  clwTheta n K + (j : ℝ) * clwLambda n K -
    (if 0 ∈ K ∧ 1 ∉ K ∧ 2 ∉ K ∧ j = 0 then 2*(n:ℝ)^2*((n:ℝ)+1)
     else if 0 ∈ K ∧ 1 ∈ K ∧ 2 ∉ K ∧ j = 0 then 2*(n:ℝ)*((n:ℝ)+1)^2 else 0)

set_option maxHeartbeats 4000000 in
theorem AuxSF_P000 (n : ℕ) (hn : 2 ≤ n) (K1 K2 : Finset (Fin 3)) (w p q : ℕ) (hw : w = 0) (hp : p = 0) (hq : q = 0)
    (hs : w + p + q ≤ n) :
    AuxSF_G n (K1 ∪ K2) (w + p + q) + AuxSF_G n (K1 ∩ K2) w ≤
      AuxSF_G n K1 (w + p) + AuxSF_G n K2 (w + q) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((w + p + q : ℕ) : ℝ) := by
    have : ((w + p + q : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  subst hw
  subst hp
  subst hq
  push_cast at hs'
  by_cases a0 : (0 : Fin 3) ∈ K1 <;> by_cases a1 : (1 : Fin 3) ∈ K1 <;>
    by_cases a2 : (2 : Fin 3) ∈ K1 <;> by_cases b0 : (0 : Fin 3) ∈ K2 <;>
    by_cases b1 : (1 : Fin 3) ∈ K2 <;> by_cases b2 : (2 : Fin 3) ∈ K2 <;>
    simp [AuxSF_G, clwTheta, clwLambda, a0, a1, a2, b0, b1, b2] <;>
    linarith [mul_nonneg hs' hn0, mul_nonneg hs' (pow_nonneg hn0 2), mul_nonneg hs' (pow_nonneg hn0 3), mul_nonneg hs' hd, mul_nonneg (mul_nonneg hs' hd) hn0, mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2), mul_nonneg hd hn0, mul_nonneg hd (pow_nonneg hn0 2), pow_nonneg hn0 2, pow_nonneg hn0 3]

set_option maxHeartbeats 4000000 in
theorem AuxSF_P001 (n : ℕ) (hn : 2 ≤ n) (K1 K2 : Finset (Fin 3)) (w p q : ℕ) (hw : w = 0) (hp : p = 0) (hq : 0 < q)
    (hs : w + p + q ≤ n) :
    AuxSF_G n (K1 ∪ K2) (w + p + q) + AuxSF_G n (K1 ∩ K2) w ≤
      AuxSF_G n K1 (w + p) + AuxSF_G n K2 (w + q) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((w + p + q : ℕ) : ℝ) := by
    have : ((w + p + q : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  subst hw
  subst hp
  obtain ⟨q, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  push_cast at hs'
  by_cases a0 : (0 : Fin 3) ∈ K1 <;> by_cases a1 : (1 : Fin 3) ∈ K1 <;>
    by_cases a2 : (2 : Fin 3) ∈ K1 <;> by_cases b0 : (0 : Fin 3) ∈ K2 <;>
    by_cases b1 : (1 : Fin 3) ∈ K2 <;> by_cases b2 : (2 : Fin 3) ∈ K2 <;>
    simp [AuxSF_G, clwTheta, clwLambda, a0, a1, a2, b0, b1, b2] <;>
    linarith [(Nat.cast_nonneg q : (0:ℝ) ≤ q), mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hn0, mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 2), mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 3), mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd, mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) hn0, mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) (pow_nonneg hn0 2), mul_nonneg hs' hn0, mul_nonneg hs' (pow_nonneg hn0 2), mul_nonneg hs' (pow_nonneg hn0 3), mul_nonneg hs' hd, mul_nonneg (mul_nonneg hs' hd) hn0, mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2), mul_nonneg hd hn0, mul_nonneg hd (pow_nonneg hn0 2), pow_nonneg hn0 2, pow_nonneg hn0 3]

set_option maxHeartbeats 4000000 in
theorem AuxSF_P011 (n : ℕ) (hn : 2 ≤ n) (K1 K2 : Finset (Fin 3)) (w p q : ℕ) (hw : w = 0) (hp : 0 < p) (hq : 0 < q)
    (hs : w + p + q ≤ n) :
    AuxSF_G n (K1 ∪ K2) (w + p + q) + AuxSF_G n (K1 ∩ K2) w ≤
      AuxSF_G n K1 (w + p) + AuxSF_G n K2 (w + q) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((w + p + q : ℕ) : ℝ) := by
    have : ((w + p + q : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  subst hw
  obtain ⟨p, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  push_cast at hs'
  by_cases a0 : (0 : Fin 3) ∈ K1 <;> by_cases a1 : (1 : Fin 3) ∈ K1 <;>
    by_cases a2 : (2 : Fin 3) ∈ K1 <;> by_cases b0 : (0 : Fin 3) ∈ K2 <;>
    by_cases b1 : (1 : Fin 3) ∈ K2 <;> by_cases b2 : (2 : Fin 3) ∈ K2 <;>
    simp [AuxSF_G, clwTheta, clwLambda, a0, a1, a2, b0, b1, b2] <;>
    linarith [(Nat.cast_nonneg p : (0:ℝ) ≤ p), mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hn0, mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) (pow_nonneg hn0 2), mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) (pow_nonneg hn0 3), mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hd, mul_nonneg (mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hd) hn0, mul_nonneg (mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hd) (pow_nonneg hn0 2), (Nat.cast_nonneg q : (0:ℝ) ≤ q), mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hn0, mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 2), mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 3), mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd, mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) hn0, mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) (pow_nonneg hn0 2), mul_nonneg hs' hn0, mul_nonneg hs' (pow_nonneg hn0 2), mul_nonneg hs' (pow_nonneg hn0 3), mul_nonneg hs' hd, mul_nonneg (mul_nonneg hs' hd) hn0, mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2), mul_nonneg hd hn0, mul_nonneg hd (pow_nonneg hn0 2), pow_nonneg hn0 2, pow_nonneg hn0 3]

set_option maxHeartbeats 4000000 in
theorem AuxSF_P100 (n : ℕ) (hn : 2 ≤ n) (K1 K2 : Finset (Fin 3)) (w p q : ℕ) (hw : 0 < w) (hp : p = 0) (hq : q = 0)
    (hs : w + p + q ≤ n) :
    AuxSF_G n (K1 ∪ K2) (w + p + q) + AuxSF_G n (K1 ∩ K2) w ≤
      AuxSF_G n K1 (w + p) + AuxSF_G n K2 (w + q) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((w + p + q : ℕ) : ℝ) := by
    have : ((w + p + q : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  obtain ⟨w, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
  subst hp
  subst hq
  push_cast at hs'
  by_cases a0 : (0 : Fin 3) ∈ K1 <;> by_cases a1 : (1 : Fin 3) ∈ K1 <;>
    by_cases a2 : (2 : Fin 3) ∈ K1 <;> by_cases b0 : (0 : Fin 3) ∈ K2 <;>
    by_cases b1 : (1 : Fin 3) ∈ K2 <;> by_cases b2 : (2 : Fin 3) ∈ K2 <;>
    simp [AuxSF_G, clwTheta, clwLambda, a0, a1, a2, b0, b1, b2] <;>
    linarith [(Nat.cast_nonneg w : (0:ℝ) ≤ w), mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hn0, mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) (pow_nonneg hn0 2), mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) (pow_nonneg hn0 3), mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd, mul_nonneg (mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd) hn0, mul_nonneg (mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd) (pow_nonneg hn0 2), mul_nonneg hs' hn0, mul_nonneg hs' (pow_nonneg hn0 2), mul_nonneg hs' (pow_nonneg hn0 3), mul_nonneg hs' hd, mul_nonneg (mul_nonneg hs' hd) hn0, mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2), mul_nonneg hd hn0, mul_nonneg hd (pow_nonneg hn0 2), pow_nonneg hn0 2, pow_nonneg hn0 3]

set_option maxHeartbeats 4000000 in
theorem AuxSF_P101 (n : ℕ) (hn : 2 ≤ n) (K1 K2 : Finset (Fin 3)) (w p q : ℕ) (hw : 0 < w) (hp : p = 0) (hq : 0 < q)
    (hs : w + p + q ≤ n) :
    AuxSF_G n (K1 ∪ K2) (w + p + q) + AuxSF_G n (K1 ∩ K2) w ≤
      AuxSF_G n K1 (w + p) + AuxSF_G n K2 (w + q) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((w + p + q : ℕ) : ℝ) := by
    have : ((w + p + q : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  obtain ⟨w, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
  subst hp
  obtain ⟨q, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  push_cast at hs'
  by_cases a0 : (0 : Fin 3) ∈ K1 <;> by_cases a1 : (1 : Fin 3) ∈ K1 <;>
    by_cases a2 : (2 : Fin 3) ∈ K1 <;> by_cases b0 : (0 : Fin 3) ∈ K2 <;>
    by_cases b1 : (1 : Fin 3) ∈ K2 <;> by_cases b2 : (2 : Fin 3) ∈ K2 <;>
    simp [AuxSF_G, clwTheta, clwLambda, a0, a1, a2, b0, b1, b2] <;>
    linarith [(Nat.cast_nonneg w : (0:ℝ) ≤ w), mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hn0, mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) (pow_nonneg hn0 2), mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) (pow_nonneg hn0 3), mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd, mul_nonneg (mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd) hn0, mul_nonneg (mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd) (pow_nonneg hn0 2), (Nat.cast_nonneg q : (0:ℝ) ≤ q), mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hn0, mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 2), mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 3), mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd, mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) hn0, mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) (pow_nonneg hn0 2), mul_nonneg hs' hn0, mul_nonneg hs' (pow_nonneg hn0 2), mul_nonneg hs' (pow_nonneg hn0 3), mul_nonneg hs' hd, mul_nonneg (mul_nonneg hs' hd) hn0, mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2), mul_nonneg hd hn0, mul_nonneg hd (pow_nonneg hn0 2), pow_nonneg hn0 2, pow_nonneg hn0 3]

set_option maxHeartbeats 4000000 in
theorem AuxSF_P111 (n : ℕ) (hn : 2 ≤ n) (K1 K2 : Finset (Fin 3)) (w p q : ℕ) (hw : 0 < w) (hp : 0 < p) (hq : 0 < q)
    (hs : w + p + q ≤ n) :
    AuxSF_G n (K1 ∪ K2) (w + p + q) + AuxSF_G n (K1 ∩ K2) w ≤
      AuxSF_G n K1 (w + p) + AuxSF_G n K2 (w + q) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hd : (0:ℝ) ≤ (n:ℝ) - 2 := by linarith
  have hs' : (0:ℝ) ≤ (n:ℝ) - ((w + p + q : ℕ) : ℝ) := by
    have : ((w + p + q : ℕ) : ℝ) ≤ n := by exact_mod_cast hs
    linarith
  obtain ⟨w, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  push_cast at hs'
  by_cases a0 : (0 : Fin 3) ∈ K1 <;> by_cases a1 : (1 : Fin 3) ∈ K1 <;>
    by_cases a2 : (2 : Fin 3) ∈ K1 <;> by_cases b0 : (0 : Fin 3) ∈ K2 <;>
    by_cases b1 : (1 : Fin 3) ∈ K2 <;> by_cases b2 : (2 : Fin 3) ∈ K2 <;>
    simp [AuxSF_G, clwTheta, clwLambda, a0, a1, a2, b0, b1, b2] <;>
    linarith [(Nat.cast_nonneg w : (0:ℝ) ≤ w), mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hn0, mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) (pow_nonneg hn0 2), mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) (pow_nonneg hn0 3), mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd, mul_nonneg (mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd) hn0, mul_nonneg (mul_nonneg (Nat.cast_nonneg w : (0:ℝ) ≤ w) hd) (pow_nonneg hn0 2), (Nat.cast_nonneg p : (0:ℝ) ≤ p), mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hn0, mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) (pow_nonneg hn0 2), mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) (pow_nonneg hn0 3), mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hd, mul_nonneg (mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hd) hn0, mul_nonneg (mul_nonneg (Nat.cast_nonneg p : (0:ℝ) ≤ p) hd) (pow_nonneg hn0 2), (Nat.cast_nonneg q : (0:ℝ) ≤ q), mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hn0, mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 2), mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (pow_nonneg hn0 3), mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd, mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) hn0, mul_nonneg (mul_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) hd) (pow_nonneg hn0 2), mul_nonneg hs' hn0, mul_nonneg hs' (pow_nonneg hn0 2), mul_nonneg hs' (pow_nonneg hn0 3), mul_nonneg hs' hd, mul_nonneg (mul_nonneg hs' hd) hn0, mul_nonneg (mul_nonneg hs' hd) (pow_nonneg hn0 2), mul_nonneg hd hn0, mul_nonneg hd (pow_nonneg hn0 2), pow_nonneg hn0 2, pow_nonneg hn0 3]

theorem AuxSF_key (n : ℕ) (hn : 2 ≤ n) (K1 K2 : Finset (Fin 3)) (w p q : ℕ)
    (hs : w + p + q ≤ n) :
    AuxSF_G n (K1 ∪ K2) (w + p + q) + AuxSF_G n (K1 ∩ K2) w ≤
      AuxSF_G n K1 (w + p) + AuxSF_G n K2 (w + q) := by
  have sw : ∀ (L1 L2 : Finset (Fin 3)) (a b c : ℕ), a + b + c ≤ n →
      AuxSF_G n (L2 ∪ L1) (a + c + b) + AuxSF_G n (L2 ∩ L1) a ≤
        AuxSF_G n L2 (a + c) + AuxSF_G n L1 (a + b) →
      AuxSF_G n (L1 ∪ L2) (a + b + c) + AuxSF_G n (L1 ∩ L2) a ≤
        AuxSF_G n L1 (a + b) + AuxSF_G n L2 (a + c) := by
    intro L1 L2 a b c _ h
    rw [Finset.union_comm, Finset.inter_comm, show a + b + c = a + c + b by ring]; linarith
  rcases Nat.eq_zero_or_pos w with hw | hw <;> rcases Nat.eq_zero_or_pos p with hp | hp <;>
    rcases Nat.eq_zero_or_pos q with hq | hq
  · exact AuxSF_P000 n hn K1 K2 w p q hw hp hq hs
  · exact AuxSF_P001 n hn K1 K2 w p q hw hp hq hs
  · exact sw K1 K2 w p q hs (AuxSF_P001 n hn K2 K1 w q p hw hq hp (by omega))
  · exact AuxSF_P011 n hn K1 K2 w p q hw hp hq hs
  · exact AuxSF_P100 n hn K1 K2 w p q hw hp hq hs
  · exact AuxSF_P101 n hn K1 K2 w p q hw hp hq hs
  · exact sw K1 K2 w p q hs (AuxSF_P101 n hn K2 K1 w q p hw hq hp (by omega))
  · exact AuxSF_P111 n hn K1 K2 w p q hw hp hq hs

theorem AuxSF_spU {n : ℕ} (U V : Finset (entropyParty n)) :
    specialPart (U ∪ V) = specialPart U ∪ specialPart V := by
  ext j; simp [specialPart]

theorem AuxSF_spI {n : ℕ} (U V : Finset (entropyParty n)) :
    specialPart (U ∩ V) = specialPart U ∩ specialPart V := by
  ext j; simp [specialPart]

theorem AuxSF_xc {n : ℕ} (U V : Finset (entropyParty n)) :
    xCount (U ∪ V) + xCount (U ∩ V) = xCount U + xCount V := by
  unfold xCount
  have e1 : (Finset.univ.filter (fun i : Fin n => x i ∈ U ∪ V)) =
      Finset.univ.filter (fun i : Fin n => x i ∈ U) ∪ Finset.univ.filter (fun i : Fin n => x i ∈ V) := by
    ext i; simp
  have e2 : (Finset.univ.filter (fun i : Fin n => x i ∈ U ∩ V)) =
      Finset.univ.filter (fun i : Fin n => x i ∈ U) ∩ Finset.univ.filter (fun i : Fin n => x i ∈ V) := by
    ext i; simp
  rw [e1, e2, Finset.card_union_add_card_inter]

theorem AuxSF_xle {n : ℕ} (U V : Finset (entropyParty n)) (h : U ⊆ V) :
    xCount U ≤ xCount V := by
  unfold xCount
  exact Finset.card_le_card (fun i hi => by simp at hi ⊢; exact h hi)

theorem AuxSF_xn {n : ℕ} (U : Finset (entropyParty n)) : xCount U ≤ n := by
  unfold xCount
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem AuxSF_sep (n : ℕ) (M : Finset (entropyParty n)) :
    separatingF n M = AuxSF_G n (specialPart M) (xCount M) := by
  have hx : xCount M = 0 ↔ ∀ i : Fin n, Sum.inr i ∉ M := by
    unfold xCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp [x]
  have e1 : M = {entropyLabelA} ↔
      (0 ∈ specialPart M ∧ 1 ∉ specialPart M ∧ 2 ∉ specialPart M ∧ xCount M = 0) := by
    rw [hx]
    simp only [specialPart, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro rfl; simp [entropyLabelA]
    · rintro ⟨h0, h1, h2, h3⟩
      ext y
      rcases y with j | i
      · fin_cases j <;> simp_all [entropyLabelA]
      · simp_all [entropyLabelA]
  have e2 : M = {entropyLabelA, b} ↔
      (0 ∈ specialPart M ∧ 1 ∈ specialPart M ∧ 2 ∉ specialPart M ∧ xCount M = 0) := by
    rw [hx]
    simp only [specialPart, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro rfl; simp [entropyLabelA, b]
    · rintro ⟨h0, h1, h2, h3⟩
      ext y
      rcases y with j | i
      · fin_cases j <;> simp_all [entropyLabelA, b]
      · simp_all [entropyLabelA, b]
  unfold separatingF AuxSF_G clwMu
  by_cases c1 : M = {entropyLabelA}
  · rw [if_pos c1, if_pos (e1.mp c1)]
  · rw [if_neg c1, if_neg (fun h => c1 (e1.mpr h))]
    by_cases c2 : M = {entropyLabelA, b}
    · rw [if_pos c2, if_pos (e2.mp c2)]
    · rw [if_neg c2, if_neg (fun h => c2 (e2.mpr h))]

theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) :
    IsSubmodular (separatingF n) := by
  intro U V
  rw [AuxSF_sep, AuxSF_sep, AuxSF_sep, AuxSF_sep, AuxSF_spU, AuxSF_spI]
  have h1 := AuxSF_xc U V
  have h2 := AuxSF_xle (U ∩ V) U Finset.inter_subset_left
  have h3 := AuxSF_xle (U ∩ V) V Finset.inter_subset_right
  have h4 := AuxSF_xn (U ∪ V)
  have k := AuxSF_key n hn (specialPart U) (specialPart V) (xCount (U ∩ V))
    (xCount U - xCount (U ∩ V)) (xCount V - xCount (U ∩ V)) (by omega)
  rw [show xCount (U ∩ V) + (xCount U - xCount (U ∩ V)) + (xCount V - xCount (U ∩ V)) =
      xCount (U ∪ V) by omega,
    show xCount (U ∩ V) + (xCount U - xCount (U ∩ V)) = xCount U by omega,
    show xCount (U ∩ V) + (xCount V - xCount (U ∩ V)) = xCount V by omega] at k
  exact k

end QAlgorithms.Papers.Independent.Intake100.P66

end
