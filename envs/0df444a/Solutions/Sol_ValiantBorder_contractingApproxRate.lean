-- Prove2me | solution 1 for ValiantBorder.contractingApproxRate
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:27:42.232802+00:00
-- url     : https://prove2.me/submissions/3ebd373f-b11a-4aef-829e-e4ab833d2310

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Theorems.Thm_ValiantBorder_contractingDiscrete
/-! Based on Claude (Anthropic), *VP ≠ VNP over every field*, November 23, 2026.
Original Lean sources at `anthropics/formal-math`, revision
`11b6c7e3c927df2658f513b6b68ea7f8929c62c5`, under Apache-2.0.
The contracting accelerator bound appears in `Paper/ApproxScales.lean` and
the exponent calculation in `Paper/Scales.lean`. -/

private def lg (n : ℕ) : ℕ := Nat.log 2 n + 1

private theorem quasi_of_exponents {P : ℕ → ℕ → Prop} (hmono : ∀ M s t, s ≤ t → P M s → P M t) {C M₁ : ℕ}
    (h : ∀ M ≥ M₁, ∀ a : ℕ, lg M ^ (C * a) ≤ M → ¬ P M (M ^ a)) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, P m s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s := by
  refine ⟨1 / (4 * (C + 1)), by positivity, ?_⟩
  have ht : Filter.Tendsto (fun m : ℕ => Real.logb 2 m) Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have ho := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < Real.log 2 / (4 * C + 4) by positivity)
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 ((ht.eventually ho).and (ht.eventually_ge_atTop 2))
  refine ⟨M₀ + M₁ + 2, fun m hm s hs => ?_⟩
  obtain ⟨h1, hL⟩ := hM₀ m (by omega)
  set L := Real.logb 2 m with hLd
  set l := Real.logb 2 L with hld
  have hl1 : 1 ≤ l := by
    rw [hld, Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
    exact hL
  have hlb : (4 * (C : ℝ) + 4) * l ≤ L := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (Real.log_nonneg (by linarith)),
      abs_of_nonneg (by linarith)] at h1
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : l ≤ L / (4 * C + 4) := by
      rw [hld, Real.logb, div_le_iff₀ hlog]
      calc Real.log L ≤ _ := h1
        _ = _ := by field_simp
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  obtain ⟨a, ha⟩ : ∃ a, a = ⌈1 / (4 * ((C : ℝ) + 1)) * L / l⌉₊ := ⟨_, rfl⟩
  have ha1 : (a : ℝ) ≤ 1 / (4 * ((C : ℝ) + 1)) * L / l + 1 := ha ▸ (Nat.ceil_lt_add_one (by positivity)).le
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlgR : (0 : ℝ) < lg m := by exact_mod_cast Nat.succ_pos _
  by_contra hb
  push Not at hb
  have hlg : Real.logb 2 (lg m) ≤ 2 * l := by
    have e : (lg m : ℝ) ≤ L ^ 2 := by
      have : ((Nat.log 2 m + 1 : ℕ) : ℝ) ≤ L + 1 := by
        push_cast
        exact add_le_add (Real.natLog_le_logb m 2) le_rfl
      calc (lg m : ℝ) ≤ L + 1 := this
        _ ≤ L ^ 2 := by nlinarith
    calc Real.logb 2 (lg m) ≤ Real.logb 2 (L ^ 2) := Real.logb_le_logb_of_le (by norm_num) hlgR e
      _ = 2 * l := by rw [Real.logb_pow]; push_cast; rfl
  have hkey : lg m ^ (C * a) ≤ m := by
    have key : ((C * a : ℕ) : ℝ) * Real.logb 2 (lg m) ≤ L := by
      push_cast
      calc (C : ℝ) * a * Real.logb 2 (lg m) ≤ C * (1 / (4 * ((C : ℝ) + 1)) * L / l + 1) * (2 * l) := by
            gcongr
            exact Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.succ_pos _)
        _ = (C : ℝ) / (C + 1) * (L / 2) + 2 * C * l := by
            field_simp
            ring
        _ ≤ 1 * (L / 2) + 2 * C * l := by
            gcongr
            rw [div_le_one (by positivity)]
            linarith
        _ ≤ L := by linarith
    have h3 := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) key
    rw [hLd, Real.rpow_logb (by norm_num) (by norm_num) hmR, mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hlgR, Real.rpow_natCast] at h3
    exact_mod_cast h3
  refine h m (by omega) a hkey (hmono m s _ ?_ hs)
  have h4 : (s : ℝ) ≤ (2 : ℝ) ^ (L * a) := by
    refine hb.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    rw [pow_two, ← mul_assoc, mul_div_right_comm, mul_comm L]
    exact mul_le_mul_of_nonneg_right (ha ▸ Nat.le_ceil _) (by linarith)
  rw [Real.rpow_mul (by norm_num), hLd, Real.rpow_logb (by norm_num) (by norm_num) hmR, Real.rpow_natCast] at h4
  exact_mod_cast h4


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
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Statement.Approximates (G m) s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s := by
  obtain ⟨C, M₁, h⟩ := ValiantBorder.contractingDiscrete hK hG
  exact quasi_of_exponents (P := fun m s => Statement.Approximates (G m) s)
    (fun _ _ _ hst ⟨q, hq, hf⟩ => ⟨q, computes_mono hq hst, hf⟩) h
