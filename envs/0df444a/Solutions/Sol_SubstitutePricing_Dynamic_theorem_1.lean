-- Prove2me | solution 1 for SubstitutePricing.Dynamic.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T13:48:30.260991+00:00
-- url     : https://prove2.me/submissions/60af8c65-5527-45e8-a6f6-2197825052bf

import Mathlib
import Definitions.Def_SubstitutePricing_Dynamic_Model

set_option autoImplicit false

namespace SPD33
open SubstitutePricing.Dynamic

variable (M : Model)

lemma den_pos (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) : 0 < M.den x r := by
  unfold Model.den
  have h1 := Real.exp_pos (M.u0 / M.μ)
  have h2 : 0 ≤ ∑ j ∈ M.S x, Real.exp ((M.a j - r j) / M.μ) :=
    Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
  linarith

lemma P_of_mem {x : Fin M.n → ℕ} (r : Fin M.n → ℝ) {i : Fin M.n} (hi : i ∈ M.S x) :
    M.P x r i = Real.exp ((M.a i - r i) / M.μ) / M.den x r := by
  simp [Model.P, hi]

lemma P_nonneg (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) (i : Fin M.n) : 0 ≤ M.P x r i := by
  unfold Model.P
  split_ifs
  · exact div_nonneg (Real.exp_pos _).le (den_pos M x r).le
  · exact le_refl 0

lemma P0_nonneg (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) : 0 ≤ M.P0 x r :=
  div_nonneg (Real.exp_pos _).le (den_pos M x r).le

lemma sumP_add_P0 (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) :
    (∑ i ∈ M.S x, M.P x r i) + M.P0 x r = 1 := by
  have hd := den_pos M x r
  rw [Finset.sum_congr rfl (fun i hi => P_of_mem M r hi), ← Finset.sum_div, Model.P0,
    ← add_div, div_eq_one_iff_eq hd.ne']
  rfl

lemma obj_eq (V : (Fin M.n → ℕ) → ℝ) (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) :
    M.obj V x r = V x + M.lam * ∑ i ∈ M.S x, M.P x r i * (r i - (V x - V (M.sell x i))) := by
  have h := sumP_add_P0 M x r
  unfold Model.obj
  have e1 : ∑ i ∈ M.S x, M.P x r i * (r i - (V x - V (M.sell x i))) =
      (∑ i ∈ M.S x, r i * M.P x r i) + (∑ i ∈ M.S x, M.P x r i * V (M.sell x i))
        - (∑ i ∈ M.S x, M.P x r i) * V x := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e1]
  have h0 : M.P0 x r = 1 - ∑ i ∈ M.S x, M.P x r i := by linarith
  rw [h0]; ring

lemma sum_shift (hM : M.Assumptions) (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) (m : ℝ)
    (hm : M.marginLHS m = ∑ i ∈ M.S x, Real.exp ((M.a i - δ i) / M.μ)) :
    M.μ * ∑ i ∈ M.S x, Real.exp ((M.a i - δ i - m) / M.μ)
      = (m - M.μ) * Real.exp (M.u0 / M.μ) := by
  have hμ := hM.mu_pos
  have e : ∀ i, Real.exp ((M.a i - δ i - m) / M.μ)
      = Real.exp ((M.a i - δ i) / M.μ) * Real.exp (-(m / M.μ)) := by
    intro i; rw [← Real.exp_add]; congr 1; field_simp; ring
  simp_rw [e]
  rw [← Finset.sum_mul, ← hm, Model.marginLHS]
  have e2 : Real.exp ((m + M.u0) / M.μ) * Real.exp (-(m / M.μ)) = Real.exp (M.u0 / M.μ) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  calc M.μ * ((m / M.μ - 1) * Real.exp ((m + M.u0) / M.μ) * Real.exp (-(m / M.μ)))
      = M.μ * (m / M.μ - 1) * (Real.exp ((m + M.u0) / M.μ) * Real.exp (-(m / M.μ))) := by ring
    _ = (m - M.μ) * Real.exp (M.u0 / M.μ) := by rw [e2]; field_simp

lemma key_le (hM : M.Assumptions) (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) (m : ℝ)
    (hm : M.marginLHS m = ∑ i ∈ M.S x, Real.exp ((M.a i - δ i) / M.μ))
    (r : Fin M.n → ℝ) :
    ∑ i ∈ M.S x, M.P x r i * (r i - δ i) ≤ m - M.μ := by
  have hμ := hM.mu_pos
  have hd := den_pos M x r
  have hterm : ∀ i, Real.exp ((M.a i - r i) / M.μ) * (r i - δ i - m + M.μ)
      ≤ M.μ * Real.exp ((M.a i - δ i - m) / M.μ) := by
    intro i
    have h1 : Real.exp ((M.a i - r i) / M.μ) = Real.exp ((M.a i - δ i - m) / M.μ)
        * Real.exp (-((r i - δ i - m) / M.μ)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    have h2 : r i - δ i - m + M.μ = M.μ * ((r i - δ i - m) / M.μ + 1) := by
      field_simp
    have h3 : ((r i - δ i - m) / M.μ + 1) * Real.exp (-((r i - δ i - m) / M.μ)) ≤ 1 := by
      have ha := Real.add_one_le_exp ((r i - δ i - m) / M.μ)
      have hez : Real.exp ((r i - δ i - m) / M.μ) * Real.exp (-((r i - δ i - m) / M.μ)) = 1 := by
        rw [← Real.exp_add]; simp
      have hp := Real.exp_pos (-((r i - δ i - m) / M.μ))
      nlinarith
    rw [h1, h2]
    have hE := Real.exp_pos ((M.a i - δ i - m) / M.μ)
    calc Real.exp ((M.a i - δ i - m) / M.μ) * Real.exp (-((r i - δ i - m) / M.μ))
          * (M.μ * ((r i - δ i - m) / M.μ + 1))
        = M.μ * Real.exp ((M.a i - δ i - m) / M.μ)
          * (((r i - δ i - m) / M.μ + 1) * Real.exp (-((r i - δ i - m) / M.μ))) := by ring
      _ ≤ M.μ * Real.exp ((M.a i - δ i - m) / M.μ) * 1 :=
          mul_le_mul_of_nonneg_left h3 (mul_pos hμ hE).le
      _ = M.μ * Real.exp ((M.a i - δ i - m) / M.μ) := by ring
  have hsum := sum_shift M hM x δ m hm
  have hA : ∑ i ∈ M.S x, Real.exp ((M.a i - r i) / M.μ) * (r i - δ i)
      ≤ (m - M.μ) * M.den x r := by
    have e : ∑ i ∈ M.S x, Real.exp ((M.a i - r i) / M.μ) * (r i - δ i) =
        ∑ i ∈ M.S x, Real.exp ((M.a i - r i) / M.μ) * (r i - δ i - m + M.μ)
          + (m - M.μ) * ∑ i ∈ M.S x, Real.exp ((M.a i - r i) / M.μ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hD : M.den x r = (∑ i ∈ M.S x, Real.exp ((M.a i - r i) / M.μ))
        + Real.exp (M.u0 / M.μ) := rfl
    rw [e, hD]
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ M.S x) => hterm i)
    rw [← Finset.mul_sum, hsum] at hs
    nlinarith
  rw [Finset.sum_congr rfl (fun i hi => by rw [P_of_mem M r hi])]
  calc ∑ i ∈ M.S x, Real.exp ((M.a i - r i) / M.μ) / M.den x r * (r i - δ i)
      = (∑ i ∈ M.S x, Real.exp ((M.a i - r i) / M.μ) * (r i - δ i)) / M.den x r := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun i _ => by ring)
    _ ≤ m - M.μ := by rw [div_le_iff₀ hd]; exact hA

lemma root_ge (hM : M.Assumptions) {m σ : ℝ} (hσ : 0 ≤ σ) (h : M.marginLHS m = σ) :
    M.μ ≤ m := by
  have hμ := hM.mu_pos
  by_contra hlt
  push Not at hlt
  have h1 : m / M.μ - 1 < 0 := by
    rw [sub_neg, div_lt_one hμ]; exact hlt
  have h2 := mul_neg_of_neg_of_pos h1 (Real.exp_pos ((m + M.u0) / M.μ))
  unfold Model.marginLHS at h
  linarith

lemma key_eq (hM : M.Assumptions) (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) (m : ℝ)
    (hm : M.marginLHS m = ∑ i ∈ M.S x, Real.exp ((M.a i - δ i) / M.μ))
    (r : Fin M.n → ℝ) (hr : ∀ i ∈ M.S x, r i = δ i + m) :
    ∑ i ∈ M.S x, M.P x r i * (r i - δ i) = m - M.μ ∧ m * M.P0 x r = M.μ := by
  have hμ := hM.mu_pos
  have hσ : 0 ≤ ∑ i ∈ M.S x, Real.exp ((M.a i - δ i) / M.μ) :=
    Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  have hmμ := root_ge M hM hσ hm
  have hT := sum_shift M hM x δ m hm
  have hE : ∀ i ∈ M.S x, Real.exp ((M.a i - r i) / M.μ) = Real.exp ((M.a i - δ i - m) / M.μ) := by
    intro i hi; rw [hr i hi]; congr 1; ring
  have hD : M.den x r = (∑ i ∈ M.S x, Real.exp ((M.a i - δ i - m) / M.μ))
      + Real.exp (M.u0 / M.μ) := by
    show (∑ i ∈ M.S x, Real.exp ((M.a i - r i) / M.μ)) + Real.exp (M.u0 / M.μ) = _
    rw [Finset.sum_congr rfl hE]
  have hd := den_pos M x r
  rw [hD] at hd
  have hw := Real.exp_pos (M.u0 / M.μ)
  constructor
  · rw [Finset.sum_congr rfl (fun i hi => by rw [P_of_mem M r hi, hE i hi, hD, hr i hi])]
    have e : ∑ i ∈ M.S x, Real.exp ((M.a i - δ i - m) / M.μ)
        / ((∑ i ∈ M.S x, Real.exp ((M.a i - δ i - m) / M.μ)) + Real.exp (M.u0 / M.μ))
          * (δ i + m - δ i)
        = (∑ i ∈ M.S x, Real.exp ((M.a i - δ i - m) / M.μ)) * m
          / ((∑ i ∈ M.S x, Real.exp ((M.a i - δ i - m) / M.μ)) + Real.exp (M.u0 / M.μ)) := by
      rw [Finset.sum_mul, Finset.sum_div]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e, div_eq_iff hd.ne']
    linear_combination hT
  · unfold Model.P0
    rw [hD, mul_div_assoc', div_eq_iff hd.ne']
    linear_combination (-1 : ℝ) * hT

lemma root_exists (hM : M.Assumptions) {σ : ℝ} (hσ : 0 ≤ σ) : ∃ m, M.marginLHS m = σ := by
  have hμ := hM.mu_pos
  have hc0 : 0 ≤ M.μ * σ * Real.exp (-(M.u0 / M.μ)) :=
    mul_nonneg (mul_nonneg hμ.le hσ) (Real.exp_pos _).le
  have hK : M.μ ≤ M.μ + M.μ * σ * Real.exp (-(M.u0 / M.μ)) := by linarith
  have hf : M.marginLHS = fun m => (m / M.μ - 1) * Real.exp ((m + M.u0) / M.μ) := rfl
  have hcont : ContinuousOn M.marginLHS
      (Set.Icc M.μ (M.μ + M.μ * σ * Real.exp (-(M.u0 / M.μ)))) := by
    rw [hf]; exact (by fun_prop : Continuous _).continuousOn
  have h0 : M.marginLHS M.μ = 0 := by simp [Model.marginLHS, div_self hμ.ne']
  have hKv : σ ≤ M.marginLHS (M.μ + M.μ * σ * Real.exp (-(M.u0 / M.μ))) := by
    unfold Model.marginLHS
    have e : (M.μ + M.μ * σ * Real.exp (-(M.u0 / M.μ))) / M.μ - 1
        = σ * Real.exp (-(M.u0 / M.μ)) := by field_simp; ring
    rw [e]
    have hle : Real.exp (M.u0 / M.μ)
        ≤ Real.exp ((M.μ + M.μ * σ * Real.exp (-(M.u0 / M.μ)) + M.u0) / M.μ) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff_of_pos_right hμ]; linarith
    have hinv : Real.exp (-(M.u0 / M.μ)) * Real.exp (M.u0 / M.μ) = 1 := by
      rw [← Real.exp_add]; simp
    have hp : 0 ≤ σ * Real.exp (-(M.u0 / M.μ)) := mul_nonneg hσ (Real.exp_pos _).le
    calc σ = σ * Real.exp (-(M.u0 / M.μ)) * Real.exp (M.u0 / M.μ) := by
          rw [mul_assoc, hinv, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hle hp
  obtain ⟨m, _, hm⟩ := intermediate_value_Icc hK hcont ⟨by rw [h0]; exact hσ, hKv⟩
  exact ⟨m, hm⟩

lemma root_unique (hM : M.Assumptions) {σ m1 m2 : ℝ} (hσ : 0 ≤ σ)
    (h1 : M.marginLHS m1 = σ) (h2 : M.marginLHS m2 = σ) : m1 = m2 := by
  have a1 := root_ge M hM hσ h1
  have a2 := root_ge M hM hσ h2
  have hμ := hM.mu_pos
  have mono : ∀ a b, M.μ ≤ a → a < b → M.marginLHS a < M.marginLHS b := by
    intro a b ha hab
    unfold Model.marginLHS
    have e1 : 0 ≤ a / M.μ - 1 := by
      rw [sub_nonneg, le_div_iff₀ hμ]; linarith
    have e2 : a / M.μ - 1 < b / M.μ - 1 := by
      have := div_lt_div_of_pos_right hab hμ; linarith
    have e3 : Real.exp ((a + M.u0) / M.μ) < Real.exp ((b + M.u0) / M.μ) :=
      Real.exp_lt_exp.mpr (div_lt_div_of_pos_right (by linarith) hμ)
    have hp := Real.exp_pos ((a + M.u0) / M.μ)
    have q1 := mul_lt_mul_of_pos_right e2 hp
    have q2 := mul_lt_mul_of_pos_left e3 (show 0 < b / M.μ - 1 by linarith)
    linarith
  rcases lt_trichotomy m1 m2 with h | h | h
  · have := mono _ _ a1 h; linarith
  · exact h
  · have := mono _ _ a2 h; linarith

lemma sell_comm (x : Fin M.n → ℕ) (i j : Fin M.n) :
    M.sell (M.sell x i) j = M.sell (M.sell x j) i := by
  by_cases hij : i = j
  · subst hij; rfl
  · funext k
    by_cases hki : k = i
    · subst hki
      simp [Model.sell, Function.update_apply, hij, Ne.symm hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [Model.sell, Function.update_apply, hki, Ne.symm hki, hij, Ne.symm hij]
      · simp [Model.sell, Function.update_apply, hki, hkj]

lemma real_ineq {lam w0 ε T A1 A2 A2' Vx Vy R : ℝ} (hl0 : 0 < lam) (hl1 : lam ≤ 1)
    (hw : 0 < w0) (hε : 0 < ε) (hT : 0 ≤ T) (hA : A2 ≤ A2') (hV : Vy ≤ Vx)
    (hR : A1 + A2 + w0 * Vy ≤ (R + Vy) * (T + w0)) :
    lam * (A1 / (T + w0)) + lam * (A2 / (T + w0)) + (lam * (w0 / (T + w0)) + 1 - lam) * Vy ≤
    lam * (R * (ε / (ε + T + w0)) + A1 / (ε + T + w0))
      + lam * (ε / (ε + T + w0) * Vy + A2' / (ε + T + w0))
      + (lam * (w0 / (ε + T + w0)) + 1 - lam) * Vx := by
  have hDy : 0 < T + w0 := by linarith
  have hDx : 0 < ε + T + w0 := by linarith
  have c1 : 0 ≤ lam * (w0 / (ε + T + w0)) + 1 - lam := by
    have : 0 ≤ lam * (w0 / (ε + T + w0)) := mul_nonneg hl0.le (div_nonneg hw.le hDx.le)
    linarith
  have s1 := mul_le_mul_of_nonneg_left hV c1
  have s2 : lam * (A2 / (ε + T + w0)) ≤ lam * (A2' / (ε + T + w0)) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hA hDx.le) hl0.le
  have key : (A1 + A2 + w0 * Vy) / (T + w0)
      ≤ (A1 + A2 + w0 * Vy + ε * (R + Vy)) / (ε + T + w0) := by
    rw [div_le_div_iff₀ hDy hDx]
    nlinarith [mul_le_mul_of_nonneg_left hR hε.le]
  have e1 : lam * (A1 / (T + w0)) + lam * (A2 / (T + w0)) + (lam * (w0 / (T + w0)) + 1 - lam) * Vy
      = lam * ((A1 + A2 + w0 * Vy) / (T + w0)) + (1 - lam) * Vy := by
    field_simp; ring
  have e2 : lam * (R * (ε / (ε + T + w0)) + A1 / (ε + T + w0))
      + lam * (ε / (ε + T + w0) * Vy + A2 / (ε + T + w0))
      + (lam * (w0 / (ε + T + w0)) + 1 - lam) * Vy
      = lam * ((A1 + A2 + w0 * Vy + ε * (R + Vy)) / (ε + T + w0)) + (1 - lam) * Vy := by
    field_simp; ring
  have s3 := mul_le_mul_of_nonneg_left key hl0.le
  have s4 : lam * (ε / (ε + T + w0) * Vy + A2 / (ε + T + w0))
      ≤ lam * (ε / (ε + T + w0) * Vy + A2' / (ε + T + w0)) := by
    have : A2 / (ε + T + w0) ≤ A2' / (ε + T + w0) := div_le_div_of_nonneg_right hA hDx.le
    nlinarith
  linarith

lemma mono_step (hM : M.Assumptions) (V : (Fin M.n → ℕ) → ℝ)
    (hV : ∀ z k, k ∈ M.S z → V (M.sell z k) ≤ V z) (x : Fin M.n → ℕ) (i : Fin M.n)
    (hi : i ∈ M.S x) (r : Fin M.n → ℝ) (hr : r ∈ M.feasible) :
    ∃ r' ∈ M.feasible, M.obj V (M.sell x i) r ≤ M.obj V x r' := by
  have hμ := hM.mu_pos
  have hl0 := hM.lam_pos
  have hl1 := hM.lam_le_one
  have hxi : 0 < x i := by simpa [Model.S] using hi
  have hmemS : ∀ (z : Fin M.n → ℕ) k, k ∈ M.S z ↔ 0 < z k := fun z k => by simp [Model.S]
  have hsell_i : ∀ j, j ≠ i → M.sell x j i = x i := fun j hj => by
    simp [Model.sell, Function.update_apply, Ne.symm hj]
  -- termwise comparison of continuation values
  have hcont : ∀ j, j ≠ i → V (M.sell (M.sell x i) j) ≤ V (M.sell x j) := by
    intro j hj
    rw [sell_comm M x i j]
    exact hV _ i ((hmemS _ _).2 (by rw [hsell_i j hj]; exact hxi))
  rcases Nat.lt_or_ge 1 (x i) with h2 | h1
  · -- x i ≥ 2 : same in-stock set
    have hS : M.S (M.sell x i) = M.S x := by
      ext k
      rw [hmemS, hmemS]
      by_cases hk : k = i
      · subst hk; simp [Model.sell]; omega
      · simp [Model.sell, Function.update_apply, hk]
    have hden : M.den (M.sell x i) r = M.den x r := by simp only [Model.den, hS]
    have hP : ∀ j, M.P (M.sell x i) r j = M.P x r j := by
      intro j; simp only [Model.P, hden, hS]
    have hP0 : M.P0 (M.sell x i) r = M.P0 x r := by simp only [Model.P0, hden]
    refine ⟨r, hr, ?_⟩
    unfold Model.obj
    rw [hS, hP0]
    simp only [hP]
    have c1 : 0 ≤ M.lam * M.P0 x r + 1 - M.lam := by
      have := mul_nonneg hl0.le (P0_nonneg M x r); linarith
    have t1 : ∑ j ∈ M.S x, M.P x r j * V (M.sell (M.sell x i) j)
        ≤ ∑ j ∈ M.S x, M.P x r j * V (M.sell x j) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (P_nonneg M x r j)
      by_cases hji : j = i
      · subst hji
        have := hV (M.sell x j) j (by rw [hS]; exact hj)
        exact this
      · exact hcont j hji
    have t2 := mul_le_mul_of_nonneg_left (hV x i hi) c1
    have t3 := mul_le_mul_of_nonneg_left t1 hl0.le
    linarith
  · -- x i = 1 : i leaves the in-stock set
    have hx1 : x i = 1 := by omega
    have hiy : i ∉ M.S (M.sell x i) := by
      rw [hmemS]; simp [Model.sell, hx1]
    have hSx : M.S x = insert i (M.S (M.sell x i)) := by
      ext k
      rw [Finset.mem_insert, hmemS, hmemS]
      by_cases hk : k = i
      · subst hk; simp [hxi]
      · simp [Model.sell, Function.update_apply, hk]
    have hne : ∀ j ∈ M.S (M.sell x i), j ≠ i := fun j hj h => hiy (h ▸ hj)
    have hjx : ∀ j ∈ M.S (M.sell x i), j ∈ M.S x := fun j hj => by
      rw [hSx]; exact Finset.mem_insert_of_mem hj
    set y := M.sell x i with hy
    set w0 := Real.exp (M.u0 / M.μ) with hw0
    set T := ∑ j ∈ M.S y, Real.exp ((M.a j - r j) / M.μ) with hT
    set A1 := ∑ j ∈ M.S y, r j * Real.exp ((M.a j - r j) / M.μ) with hA1
    set A2 := ∑ j ∈ M.S y, Real.exp ((M.a j - r j) / M.μ) * V (M.sell y j) with hA2
    set A2' := ∑ j ∈ M.S y, Real.exp ((M.a j - r j) / M.μ) * V (M.sell x j) with hA2'
    set R := max 0 ((A1 + A2 + w0 * V y) / (T + w0) - V y) with hR
    set r' := Function.update r i R with hr'
    set ε := Real.exp ((M.a i - R) / M.μ) with hε
    have hr'i : r' i = R := by simp [r']
    have hr'j : ∀ j ∈ M.S y, r' j = r j := fun j hj => by
      simp [r', Function.update_apply, hne j hj]
    have hT0 : 0 ≤ T := Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    have hwpos : 0 < w0 := Real.exp_pos _
    have hDy : M.den y r = T + w0 := rfl
    have hDx : M.den x r' = ε + T + w0 := by
      show (∑ j ∈ M.S x, Real.exp ((M.a j - r' j) / M.μ)) + Real.exp (M.u0 / M.μ) = _
      rw [hSx, Finset.sum_insert hiy, hr'i,
        Finset.sum_congr rfl (fun j hj => by rw [hr'j j hj])]
    refine ⟨r', ?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · subst hj; rw [hr'i]; exact le_max_left _ _
      · simp only [r', Function.update_apply, hj, if_false]; exact hr j
    · have hobjy : M.obj V y r = M.lam * (A1 / (T + w0)) + M.lam * (A2 / (T + w0))
          + (M.lam * (w0 / (T + w0)) + 1 - M.lam) * V y := by
        unfold Model.obj Model.P0
        rw [hDy]
        have u1 : ∑ j ∈ M.S y, r j * M.P y r j = A1 / (T + w0) := by
          rw [hA1, Finset.sum_div]
          exact Finset.sum_congr rfl (fun j hj => by rw [P_of_mem M r hj, hDy]; ring)
        have u2 : ∑ j ∈ M.S y, M.P y r j * V (M.sell y j) = A2 / (T + w0) := by
          rw [hA2, Finset.sum_div]
          exact Finset.sum_congr rfl (fun j hj => by rw [P_of_mem M r hj, hDy]; ring)
        rw [u1, u2]
      have hobjx : M.obj V x r' = M.lam * (R * (ε / (ε + T + w0)) + A1 / (ε + T + w0))
          + M.lam * (ε / (ε + T + w0) * V y + A2' / (ε + T + w0))
          + (M.lam * (w0 / (ε + T + w0)) + 1 - M.lam) * V x := by
        unfold Model.obj Model.P0
        rw [hDx]
        have hPi : M.P x r' i = ε / (ε + T + w0) := by
          rw [P_of_mem M r' hi, hDx, hr'i]
        have u1 : ∑ j ∈ M.S y, r' j * M.P x r' j = A1 / (ε + T + w0) := by
          rw [hA1, Finset.sum_div]
          exact Finset.sum_congr rfl (fun j hj => by
            rw [P_of_mem M r' (hjx j hj), hDx, hr'j j hj]; ring)
        have u2 : ∑ j ∈ M.S y, M.P x r' j * V (M.sell x j) = A2' / (ε + T + w0) := by
          rw [hA2', Finset.sum_div]
          exact Finset.sum_congr rfl (fun j hj => by
            rw [P_of_mem M r' (hjx j hj), hDx, hr'j j hj]; ring)
        rw [hSx, Finset.sum_insert hiy, Finset.sum_insert hiy, hPi, hr'i, u1, u2]
      rw [hobjy, hobjx]
      have hAA : A2 ≤ A2' := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hcont j (hne j hj)) (Real.exp_pos _).le
      apply real_ineq hl0 hl1 hwpos (Real.exp_pos _) hT0 hAA (hV x i hi)
      have hmx := le_max_right 0 ((A1 + A2 + w0 * V y) / (T + w0) - V y)
      rw [← hR] at hmx
      have : (A1 + A2 + w0 * V y) / (T + w0) ≤ R + V y := by linarith
      exact (div_le_iff₀ (by linarith)).mp this

/-- candidate prices for a general continuation value -/
def rs (V : (Fin M.n → ℕ) → ℝ) (x : Fin M.n → ℕ) (m : ℝ) : Fin M.n → ℝ :=
  fun i => if i ∈ M.S x then (V x - V (M.sell x i)) + m else 0

lemma closed (hM : M.Assumptions) (V : (Fin M.n → ℕ) → ℝ)
    (hV : ∀ z k, k ∈ M.S z → V (M.sell z k) ≤ V z) (x : Fin M.n → ℕ) (m : ℝ)
    (hm : M.marginLHS m
      = ∑ i ∈ M.S x, Real.exp ((M.a i - (V x - V (M.sell x i))) / M.μ)) :
    rs M V x m ∈ M.feasible ∧ IsGreatest (M.obj V x '' M.feasible) (M.obj V x (rs M V x m)) ∧
    M.obj V x (rs M V x m) = V x + M.lam * (m - M.μ) ∧ m * M.P0 x (rs M V x m) = M.μ := by
  have hσ : 0 ≤ ∑ i ∈ M.S x, Real.exp ((M.a i - (V x - V (M.sell x i))) / M.μ) :=
    Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  have hmμ := root_ge M hM hσ hm
  have hμ := hM.mu_pos
  have hlam := hM.lam_pos
  obtain ⟨e1, e2⟩ := key_eq M hM x (fun i => V x - V (M.sell x i)) m hm (rs M V x m)
    (fun i hi => by simp [rs, hi])
  have hval : M.obj V x (rs M V x m) = V x + M.lam * (m - M.μ) := by
    rw [obj_eq, e1]
  have hfeas : rs M V x m ∈ M.feasible := by
    intro i
    simp only [rs]
    split_ifs with hi
    · have := hV x i hi; linarith
    · exact le_refl 0
  refine ⟨hfeas, ⟨⟨_, hfeas, rfl⟩, ?_⟩, hval, e2⟩
  rintro _ ⟨r, _, rfl⟩
  rw [hval, obj_eq]
  have h1 := key_le M hM x (fun i => V x - V (M.sell x i)) m hm r
  have h2 := mul_le_mul_of_nonneg_left h1 hlam.le
  linarith

lemma pi_succ_facts (hM : M.Assumptions) (s : ℕ)
    (hmono : ∀ z k, k ∈ M.S z → M.pi s (M.sell z k) ≤ M.pi s z) (x : Fin M.n → ℕ) (m : ℝ)
    (hm : M.marginLHS m = M.sigma (s + 1) x) :
    M.rstar (s + 1) x m ∈ M.feasible ∧
    IsMaxOn (M.obj (M.pi s) x) M.feasible (M.rstar (s + 1) x m) ∧
    M.pi (s + 1) x = M.obj (M.pi s) x (M.rstar (s + 1) x m) ∧
    M.obj (M.pi s) x (M.rstar (s + 1) x m) = M.pi s x + M.lam * (m - M.μ) ∧
    m * M.P0 x (M.rstar (s + 1) x m) = M.μ := by
  have hr : M.rstar (s + 1) x m = rs M (M.pi s) x m := by
    funext i; simp [Model.rstar, rs, Model.delta]
  have hm' : M.marginLHS m
      = ∑ i ∈ M.S x, Real.exp ((M.a i - (M.pi s x - M.pi s (M.sell x i))) / M.μ) := by
    rw [hm]; simp [Model.sigma, Model.delta]
  obtain ⟨h1, h2, h3, h4⟩ := closed M hM (M.pi s) hmono x m hm'
  rw [hr]
  refine ⟨h1, ?_, ?_, h3, h4⟩
  · exact isMaxOn_iff.mpr (fun r hr => h2.2 ⟨r, hr, rfl⟩)
  · show sSup ((M.obj (M.pi s) x) '' M.feasible) = _
    exact h2.csSup_eq

lemma sigma_nonneg (u : ℕ) (w : Fin M.n → ℕ) : 0 ≤ M.sigma u w :=
  Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)

lemma mono_all (hM : M.Assumptions) :
    ∀ s z k, k ∈ M.S z → M.pi s (M.sell z k) ≤ M.pi s z := by
  intro s
  induction s with
  | zero => intro z k _; simp [Model.pi]
  | succ s ih =>
    intro z k hk
    obtain ⟨my, hmy⟩ := root_exists M hM (sigma_nonneg M (s + 1) (M.sell z k))
    obtain ⟨mz, hmz⟩ := root_exists M hM (sigma_nonneg M (s + 1) z)
    obtain ⟨fy, -, ey, -⟩ := pi_succ_facts M hM s ih _ my hmy
    obtain ⟨-, mz', ez, -⟩ := pi_succ_facts M hM s ih z mz hmz
    obtain ⟨r', hr', hle⟩ := mono_step M hM (M.pi s) ih z k hk _ fy
    rw [ey, ez]
    exact hle.trans (isMaxOn_iff.mp mz' r' hr')

end SPD33

open SubstitutePricing.Dynamic in
theorem solution (M : Model) (hM : M.Assumptions) (t : ℕ) (ht : 1 ≤ t)
    (x : Fin M.n → ℕ) :
    (∃! m : ℝ, M.marginLHS m = M.sigma t x) ∧
    (∀ m : ℝ, M.marginLHS m = M.sigma t x →
      M.rstar t x m ∈ M.feasible ∧
      IsMaxOn (M.obj (M.pi (t - 1)) x) M.feasible (M.rstar t x m) ∧
      M.pi t x = M.obj (M.pi (t - 1)) x (M.rstar t x m) ∧
      m * M.P0 x (M.rstar t x m) = M.μ) ∧
    (∀ ms : ℕ → ℝ,
      (∀ s ∈ Finset.Icc 1 t, M.marginLHS (ms s) = M.sigma s x) →
      M.pi t x = M.lam * ∑ s ∈ Finset.Icc 1 t, (ms s - M.μ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have hmono := SPD33.mono_all M hM
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := SPD33.root_exists M hM (SPD33.sigma_nonneg M (k + 1) x)
    exact ⟨m, hm, fun m' hm' => SPD33.root_unique M hM (SPD33.sigma_nonneg M (k + 1) x) hm' hm⟩
  · intro m hm
    obtain ⟨h1, h2, h3, -, h5⟩ := SPD33.pi_succ_facts M hM k (hmono k) x m hm
    simp only [Nat.add_sub_cancel]
    exact ⟨h1, h2, h3, h5⟩
  · intro ms hms
    have tel : ∀ u, (∀ v ∈ Finset.Icc 1 u, M.marginLHS (ms v) = M.sigma v x) →
        M.pi u x = M.lam * ∑ v ∈ Finset.Icc 1 u, (ms v - M.μ) := by
      intro u
      induction u with
      | zero => intro _; simp [Model.pi]
      | succ u ih =>
        intro h
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ u + 1)]
        have hu := h (u + 1) (Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩)
        obtain ⟨-, -, e3, e4, -⟩ := SPD33.pi_succ_facts M hM u (hmono u) x _ hu
        have hih := ih (fun v hv => h v (Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hv).1, by have := (Finset.mem_Icc.mp hv).2; omega⟩))
        rw [e3, e4, hih]
        ring
    exact tel _ hms
