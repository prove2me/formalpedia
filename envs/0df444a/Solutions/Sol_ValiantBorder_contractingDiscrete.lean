-- Prove2me | solution 1 for ValiantBorder.contractingDiscrete
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:34:09.171809+00:00
-- url     : https://prove2.me/submissions/c220933a-60f4-4931-8966-622e8d86d210

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Theorems.Thm_ValiantBorder_contractingAcceleratorObstruction
import Theorems.Thm_ValiantBorder_circuitsToAccelerators
/-! Source: Claude (Anthropic), *VP ≠ VNP over every field* (2026),
`anthropics/formal-math` commit 11b6c7e3c927df2658f513b6b68ea7f8929c62c5.
Adapted with attribution under the Apache-2.0 license. -/

open NS1
private theorem lg_mono {a b : ℕ} (h : a ≤ b) : lg a ≤ lg b := Nat.succ_le_succ (Nat.log_mono_right h)

private theorem le_lg_of_two_pow_le {n k : ℕ} (h : 2 ^ k ≤ n) : k + 1 ≤ lg n :=
  Nat.succ_le_succ (Nat.le_log_of_pow_le (by norm_num) h)

private theorem two_pow_lg_le {n : ℕ} (hn : n ≠ 0) : 2 ^ (lg n - 1) ≤ n := by
  unfold lg
  rw [Nat.add_sub_cancel]
  exact Nat.pow_log_le_self 2 hn

/-- Powers of the logarithm are small. -/
private theorem poly_lg (c k : ℕ) : ∃ n₀, ∀ n, n₀ ≤ n → c * lg n ^ k ≤ n := by
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt k (show (1 : ℝ) < 2 by norm_num)
  have h2 : ∀ᶠ L : ℕ in Filter.atTop, (L : ℝ) ^ k / 2 ^ L < 1 / (2 * (c + 1)) :=
    h1.eventually (gt_mem_nhds (by positivity))
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 h2
  refine ⟨2 ^ L₀ + 1, fun n hn => ?_⟩
  have hp : 1 ≤ 2 ^ L₀ := Nat.one_le_two_pow
  have hn0 : n ≠ 0 := by omega
  have hL : L₀ ≤ lg n := (Nat.le_succ _).trans (le_lg_of_two_pow_le (by omega))
  have h3 := hL₀ (lg n) hL
  have h4 := two_pow_lg_le hn0
  have hlg : 1 ≤ lg n := by unfold lg; omega
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h3
  have h5 : (c : ℝ) * (lg n : ℝ) ^ k ≤ 2 ^ (lg n - 1) := by
    have e : (2 : ℝ) ^ lg n = 2 * 2 ^ (lg n - 1) := by
      have : lg n = lg n - 1 + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    rw [e] at h3
    have : (0 : ℝ) ≤ (lg n : ℝ) ^ k := by positivity
    nlinarith
  have h6 : c * lg n ^ k ≤ 2 ^ (lg n - 1) := by exact_mod_cast h5
  exact h6.trans h4

private theorem exists_root (B Z₀ M : ℕ) (hB : 0 < B) (hM : Z₀ ^ B ≤ M) : ∃ Z, Z₀ ≤ Z ∧ Z ^ B ≤ M ∧ M < (Z + 1) ^ B := by
  have hex : ∃ n, M < n ^ B := ⟨M + 1, lt_of_lt_of_le (Nat.lt_succ_self M) (Nat.le_self_pow (by omega) _)⟩
  obtain ⟨n, hn, hmin⟩ : ∃ n, M < n ^ B ∧ ∀ k < n, ¬ M < k ^ B := by
    classical
    exact ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hn
    omega
  obtain ⟨Z, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨Z, ?_, not_lt.1 (hmin Z (Nat.lt_succ_self Z)), hn⟩
  by_contra hlt
  have h1 : (Z + 1) ^ B ≤ Z₀ ^ B := Nat.pow_le_pow_left (by omega) B
  have h2 : M < (Z + 1) ^ B := hn
  omega

private theorem aux3 {v : ℕ} (hv : 2 ≤ v) : v + 1 ≤ v ^ 2 := by nlinarith

private theorem lg_pow_transport {v M b E a : ℕ} (hb : b ≠ 0) (hvM : v ≤ M) (hMv : M ≤ v ^ b)
    (ha : lg M ^ (2 * b * E * a) ≤ M) (hv : lg v ^ (2 * E) ≤ v) : lg v ^ (E * (a + 1)) ≤ v := by
  have h1 : lg v ^ (2 * E * a) ≤ v := by
    refine (Nat.pow_le_pow_iff_left hb).1 ?_
    calc (lg v ^ (2 * E * a)) ^ b ≤ (lg M ^ (2 * E * a)) ^ b :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_left (lg_mono hvM) _) _
      _ = lg M ^ (2 * b * E * a) := by rw [← pow_mul]; congr 1; ring
      _ ≤ v ^ b := ha.trans hMv
  refine (Nat.pow_le_pow_iff_left (show 2 ≠ 0 by norm_num)).1 ?_
  calc (lg v ^ (E * (a + 1))) ^ 2 = lg v ^ (2 * E * a) * lg v ^ (2 * E) := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
    _ ≤ v * v := Nat.mul_le_mul h1 hv
    _ = v ^ 2 := (pow_two v).symm

private theorem exists_scale (B₀ E n : ℕ) (hB : 0 < B₀) : ∃ C M₁ : ℕ, ∀ M, M₁ ≤ M → ∀ a, lg M ^ (C * a) ≤ M →
    ∃ v, n ≤ v ∧ v ^ B₀ ≤ M ∧ M ^ a ≤ v ^ (2 * B₀ * a) ∧ lg v ^ (E * (2 * B₀ * a + 1)) ≤ v := by
  obtain ⟨n1, hn1⟩ := poly_lg 1 (2 * (E * (2 * B₀ + 1)))
  refine ⟨2 * (2 * B₀) * (E * (2 * B₀ + 1)), (n + n1 + 4) ^ B₀, fun M hM a ha => ?_⟩
  obtain ⟨v, hv, hvM, hMv⟩ := exists_root B₀ (n + n1 + 4) M hB hM
  have hM2 : M ≤ v ^ (2 * B₀) := by
    refine hMv.le.trans ((Nat.pow_le_pow_left (aux3 (show 2 ≤ v by omega)) B₀).trans (le_of_eq ?_))
    rw [← pow_mul]
  refine ⟨v, by omega, hvM, (Nat.pow_le_pow_left hM2 a).trans (le_of_eq (pow_mul _ _ _).symm), ?_⟩
  refine le_trans (Nat.pow_le_pow_right (Nat.succ_pos _) ?_) (lg_pow_transport (b := 2 * B₀) (by omega)
    ((Nat.le_self_pow (by omega) v).trans hvM) hM2 ha (by simpa using hn1 v (by omega)))
  rw [mul_assoc E (2 * B₀ + 1)]
  refine Nat.mul_le_mul_left E ?_
  calc 2 * B₀ * a + 1 ≤ (2 * B₀ + 1) * a + (2 * B₀ + 1) := by rw [add_mul]; omega
    _ = (2 * B₀ + 1) * (a + 1) := by ring


private theorem computes_mono {R : Type*} [CommSemiring R] {V : Type} {p : MvPolynomial V R} {s t : ℕ}
    (h : Statement.Computes p s) (hst : s ≤ t) : Statement.Computes p t := by
  obtain ⟨l, hl, a, ha, hla⟩ := h
  refine ⟨fun k => if k < s then l k else 0, ?_, a, by omega, by simpa [ha] using hla⟩
  intro k hk
  by_cases hs : k < s
  · simp only [if_pos hs]
    rcases hl k hs with h | h | ⟨i, hi, j, hj, he⟩ | ⟨i, hi, j, hj, he⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by simpa [hi.trans hs,hj.trans hs] using he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by simpa [hi.trans hs,hj.trans hs] using he⟩))
  · exact Or.inr (Or.inl ⟨0, by simp [hs]⟩)

theorem solution {K : Type} [Field K] (hK : Paper.Contracting K)
    {G : ∀ S, MvPolynomial (Fin S × Fin S) K} {κ : ℕ} (hG : ValiantBorder.GridComplete K G κ) :
    ∃ C M₁ : ℕ, ∀ M ≥ M₁, ∀ a : ℕ, (Nat.log 2 M + 1) ^ (C * a) ≤ M →
      ¬ Statement.Approximates (G M) (M ^ a) := by
  obtain ⟨A, θ, h, hθ, hh, C₂, v₂, hno⟩ := ValiantBorder.contractingAcceleratorObstruction hK
  obtain ⟨B₀, C₁, v₁, hB₀, hacc⟩ := ValiantBorder.circuitsToAccelerators A θ hθ (H := 16 * h) (by omega) κ
  obtain ⟨C, M₁, hscale⟩ := exists_scale B₀ ((C₂ + 1) * C₁) (v₁ + v₂ + 4) hB₀
  refine ⟨C, M₁, fun M hM a ha happ => ?_⟩
  obtain ⟨v, hv, hvM, hsize, hlog⟩ := hscale M hM a ha
  have hl1 : 1 ≤ lg v := Nat.succ_pos _
  refine hno v (by omega) (C₁ * (2 * B₀ * a + 1)) (le_trans (Nat.pow_le_pow_right hl1 ?_) hlog)
    (hacc G hG v (by omega) (2 * B₀ * a) (le_trans (Nat.pow_le_pow_right hl1 ?_) hlog) M hvM
      (let ⟨p, hp, hf⟩ := happ; ⟨p, computes_mono hp hsize, hf⟩))
  · rw [← mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ _))
  · exact Nat.mul_le_mul (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) (Nat.le_succ _)
