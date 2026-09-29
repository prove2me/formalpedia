-- Prove2me | solution 1 for ThreeOpSplitting.Convergence.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T16:49:41.921438+00:00
-- url     : https://prove2.me/submissions/bd4df8fa-f35f-4b55-8133-bad07796987c

import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Mathlib

open InnerProductSpace


namespace ThreeOpSplitting.Convergence

theorem lemma_2_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U T₁ V : H → H) (hU : IsFirmlyNonexpansive U) (hT₁ : IsFirmlyNonexpansive T₁) :
    let S : H → H := fun x => U x + T₁ (V x)
    let W : H → H := fun x => x - ((2 : ℝ) • U x + V x)
    ∀ z w : H,
      ‖S z - S w‖ ^ 2 ≤ ‖z - w‖ ^ 2 - ‖(z - S z) - (w - S w)‖ ^ 2
        - 2 * ⟪T₁ (V z) - T₁ (V w), W z - W w⟫_ℝ := by
  intro S W z w
  set a := U z - U w with ha
  set b := T₁ (V z) - T₁ (V w) with hb
  set d := z - w with hd
  set v := V z - V w with hv
  have e1 : S z - S w = a + b := by simp only [S, ha, hb]; abel
  have e2 : (z - S z) - (w - S w) = d - (a + b) := by simp only [S, ha, hb, hd]; abel
  have e3 : W z - W w = d - (2 : ℝ) • a - v := by simp only [W, ha, hd, hv]; module
  have hUa : ‖a‖ ^ 2 ≤ ⟪a, d⟫_ℝ := hU z w
  have hTb : ‖b‖ ^ 2 ≤ ⟪b, v⟫_ℝ := hT₁ (V z) (V w)
  rw [e1, e2, e3]
  clear_value a b d v
  rw [norm_sub_sq_real d (a + b), norm_add_sq_real a b, inner_add_right d a b,
    inner_sub_right b (d - (2:ℝ) • a) v, inner_sub_right b d ((2:ℝ) • a),
    real_inner_smul_right b a 2]
  have s1 : ⟪d, a⟫_ℝ = ⟪a, d⟫_ℝ := real_inner_comm _ _
  have s2 : ⟪d, b⟫_ℝ = ⟪b, d⟫_ℝ := real_inner_comm _ _
  have s3 : ⟪b, a⟫_ℝ = ⟪a, b⟫_ℝ := real_inner_comm _ _
  nlinarith

/-- `I - T` is firmly nonexpansive when `T` is. -/
lemma firm_compl {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (T : H → H)
    (hT : IsFirmlyNonexpansive T) : IsFirmlyNonexpansive (fun x => x - T x) := by
  intro x y
  have h := hT x y
  have e : (x - T x) - (y - T y) = (x - y) - (T x - T y) := by abel
  simp only
  rw [e, norm_sub_sq_real (x - y) (T x - T y), inner_sub_left (x - y) (T x - T y) (x - y),
    real_inner_self_eq_norm_sq]
  have := real_inner_comm (x - y) (T x - T y)
  linarith

/-- The key inequality for `T = threeOp γ T₁ T₂ C` with a Young parameter `ε > 0`. -/
lemma key_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T₁ T₂ C : H → H) (β γ ε : ℝ)
    (hT₁ : IsFirmlyNonexpansive T₁) (hT₂ : IsFirmlyNonexpansive T₂)
    (hC : IsCocoercive β C) (hγ0 : 0 < γ) (hε : 0 < ε) (z w : H) :
    ‖threeOp γ T₁ T₂ C z - threeOp γ T₁ T₂ C w‖ ^ 2 ≤ ‖z - w‖ ^ 2
      - (1 - ε) * ‖(z - threeOp γ T₁ T₂ C z) - (w - threeOp γ T₁ T₂ C w)‖ ^ 2
      - γ * (2 * β - γ / ε) * ‖C (T₂ z) - C (T₂ w)‖ ^ 2 := by
  set T := threeOp γ T₁ T₂ C with hTdef
  set U : H → H := fun x => x - T₂ x with hUdef
  set V : H → H := fun x => (2 : ℝ) • T₂ x - x - γ • C (T₂ x) with hVdef
  have hS : ∀ x, U x + T₁ (V x) = T x := by
    intro x; simp only [hUdef, hVdef, hTdef, threeOp]; abel
  have hW : ∀ x, x - ((2 : ℝ) • U x + V x) = γ • C (T₂ x) := by
    intro x; simp only [hUdef, hVdef]; module
  have hT1V : ∀ x, T₁ (V x) = T x - x + T₂ x := by
    intro x; rw [← hS x]; simp only [hUdef]; abel
  have h23 := lemma_2_3 U T₁ V (firm_compl T₂ hT₂) hT₁ z w
  simp only [hS, hW] at h23
  rw [hT1V, hT1V] at h23
  set c := C (T₂ z) - C (T₂ w) with hc
  set p := T₂ z - T₂ w with hp
  set e := (T z - z) - (T w - w) with he
  have hsplit : (T z - z + T₂ z) - (T w - w + T₂ w) = e + p := by rw [he, hp]; abel
  have hWd : γ • C (T₂ z) - γ • C (T₂ w) = γ • c := by rw [hc, smul_sub]
  rw [hsplit, hWd, real_inner_smul_right, inner_add_left] at h23
  -- cocoercivity
  have hcoc : β * ‖c‖ ^ 2 ≤ ⟪c, p⟫_ℝ := hC (T₂ z) (T₂ w)
  have hcp : ⟪p, c⟫_ℝ = ⟪c, p⟫_ℝ := real_inner_comm _ _
  -- Young
  have hY0 : 0 ≤ ‖ε • e + γ • c‖ ^ 2 := sq_nonneg _
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hε, abs_of_pos hγ0] at hY0
  have hY : -2 * γ * ⟪e, c⟫_ℝ ≤ ε * ‖e‖ ^ 2 + γ ^ 2 / ε * ‖c‖ ^ 2 := by
    have h1 : 0 ≤ (ε * ‖e‖) ^ 2 + 2 * (ε * (γ * ⟪e, c⟫_ℝ)) + (γ * ‖c‖) ^ 2 := hY0
    have h2 : (ε * ‖e‖) ^ 2 + 2 * (ε * (γ * ⟪e, c⟫_ℝ)) + (γ * ‖c‖) ^ 2 =
        ε * (ε * ‖e‖ ^ 2 + 2 * γ * ⟪e, c⟫_ℝ + γ ^ 2 / ε * ‖c‖ ^ 2) := by
      field_simp
    rw [h2] at h1
    have h3 := (mul_nonneg_iff_of_pos_left hε).1 h1
    linarith
  have hnorm : ‖(z - T z) - (w - T w)‖ = ‖e‖ := by
    rw [he, ← norm_neg]; congr 1; abel
  rw [hnorm]
  rw [hnorm] at h23
  have hγc : γ * (2 * β - γ / ε) * ‖c‖ ^ 2 = 2 * γ * (β * ‖c‖ ^ 2) - γ ^ 2 / ε * ‖c‖ ^ 2 := by
    field_simp
  have hγcoc := mul_le_mul_of_nonneg_left hcoc (by linarith : (0:ℝ) ≤ 2 * γ)
  nlinarith

theorem proposition_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (T₁ T₂ C : H → H) (β γ : ℝ)
    (hT₁ : IsFirmlyNonexpansive T₁) (hT₂ : IsFirmlyNonexpansive T₂)
    (hβ : 0 < β) (hC : IsCocoercive β C) (hγ0 : 0 < γ) (hγ : γ < 2 * β) :
    IsAveraged (2 * β / (4 * β - γ)) (threeOp γ T₁ T₂ C) ∧
      ∀ z w : H,
        ‖threeOp γ T₁ T₂ C z - threeOp γ T₁ T₂ C w‖ ^ 2 ≤ ‖z - w‖ ^ 2
          - (1 - 2 * β / (4 * β - γ)) / (2 * β / (4 * β - γ))
            * ‖(z - threeOp γ T₁ T₂ C z) - (w - threeOp γ T₁ T₂ C w)‖ ^ 2 := by
  set α := 2 * β / (4 * β - γ) with hα
  have hden : 0 < 4 * β - γ := by linarith
  have hα0 : 0 < α := div_pos (by linarith) hden
  have hα1 : α < 1 := by rw [hα, div_lt_one hden]; linarith
  have hβ0 : β ≠ 0 := hβ.ne'
  have hd0 : 4 * β - γ ≠ 0 := hden.ne'
  have hd0' : β * 4 - γ ≠ 0 := by intro h; apply hd0; linarith
  have hcoef : (1 - α) / α = 1 - γ / (2 * β) := by
    rw [div_eq_iff hα0.ne', hα]
    field_simp
    ring
  set T := threeOp γ T₁ T₂ C with hTdef
  have hineq : ∀ z w : H, ‖T z - T w‖ ^ 2 ≤ ‖z - w‖ ^ 2
      - (1 - α) / α * ‖(z - T z) - (w - T w)‖ ^ 2 := by
    intro z w
    have hε : 0 < γ / (2 * β) := by positivity
    have h := key_ineq T₁ T₂ C β γ (γ / (2 * β)) hT₁ hT₂ hC hγ0 hε z w
    have e : γ * (2 * β - γ / (γ / (2 * β))) = 0 := by field_simp; ring
    rw [e, zero_mul] at h
    rw [hcoef]; linarith
  refine ⟨⟨hα0, hα1, fun x => α⁻¹ • (T x - (1 - α) • x), ?_, ?_⟩, hineq⟩
  · intro z w
    have h := hineq z w
    set t := T z - T w
    set d := z - w
    have e1 : α⁻¹ • (T z - (1 - α) • z) - α⁻¹ • (T w - (1 - α) • w) =
        α⁻¹ • (t - (1 - α) • d) := by simp only [t, d]; module
    have e2 : (z - T z) - (w - T w) = d - t := by simp only [t, d]; abel
    rw [e2] at h
    rw [e1]
    clear_value t d
    rw [norm_sub_sq_real d t] at h
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hα0]
    have key : ‖t - (1 - α) • d‖ ^ 2 ≤ (α * ‖d‖) ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0:ℝ) < 1 - α)]
      have hm : α * ‖t‖ ^ 2 ≤ α * ‖d‖ ^ 2 - (1 - α) * (‖d‖ ^ 2 - 2 * ⟪d, t⟫_ℝ + ‖t‖ ^ 2) := by
        have := mul_le_mul_of_nonneg_left h hα0.le
        have e3 : α * ((1 - α) / α * (‖d‖ ^ 2 - 2 * ⟪d, t⟫_ℝ + ‖t‖ ^ 2)) =
            (1 - α) * (‖d‖ ^ 2 - 2 * ⟪d, t⟫_ℝ + ‖t‖ ^ 2) := by field_simp
        nlinarith
      have hdt : ⟪t, d⟫_ℝ = ⟪d, t⟫_ℝ := real_inner_comm _ _
      nlinarith
    have hnn : 0 ≤ α * ‖d‖ := by positivity
    have := pow_le_pow_left₀ (norm_nonneg _) (le_refl ‖t - (1 - α) • d‖) 2
    have hk : ‖t - (1 - α) • d‖ ≤ α * ‖d‖ := by
      nlinarith [sq_nonneg (‖t - (1 - α) • d‖ - α * ‖d‖), norm_nonneg (t - (1 - α) • d)]
    rw [inv_mul_le_iff₀ hα0]; exact hk
  · intro x
    simp only [smul_smul, mul_inv_cancel₀ hα0.ne', one_smul]
    abel

theorem remark_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (T₁ T₂ C : H → H) (β εbar γbar : ℝ)
    (hT₁ : IsFirmlyNonexpansive T₁) (hT₂ : IsFirmlyNonexpansive T₂)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hε0 : 0 < εbar) (hε1 : εbar < 1) (hγ0 : 0 < γbar) (hγ : γbar < 2 * β * εbar) :
    alpha εbar < 1 ∧
      ∀ z w : H,
        ‖threeOp γbar T₁ T₂ C z - threeOp γbar T₁ T₂ C w‖ ^ 2 ≤ ‖z - w‖ ^ 2
          - (1 - alpha εbar) / alpha εbar
            * ‖(z - threeOp γbar T₁ T₂ C z) - (w - threeOp γbar T₁ T₂ C w)‖ ^ 2
          - γbar * (2 * β - γbar / εbar) * ‖C (T₂ z) - C (T₂ w)‖ ^ 2 := by
  have hcoef : (1 - alpha εbar) / alpha εbar = 1 - εbar := by
    unfold alpha
    have : (2 - εbar) ≠ 0 := by linarith
    field_simp; ring
  refine ⟨?_, fun z w => ?_⟩
  · unfold alpha; rw [div_lt_one (by linarith)]; linarith
  · rw [hcoef]
    exact key_ineq T₁ T₂ C β γbar εbar hT₁ hT₂ hC hγ0 hε0 z w

end ThreeOpSplitting.Convergence

open ThreeOpSplitting.Convergence

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U T₁ V : H → H) (hU : IsFirmlyNonexpansive U) (hT₁ : IsFirmlyNonexpansive T₁) :
    let S : H → H := fun x => U x + T₁ (V x)
    let W : H → H := fun x => x - ((2 : ℝ) • U x + V x)
    ∀ z w : H,
      ‖S z - S w‖ ^ 2 ≤ ‖z - w‖ ^ 2 - ‖(z - S z) - (w - S w)‖ ^ 2
        - 2 * ⟪T₁ (V z) - T₁ (V w), W z - W w⟫_ℝ := by
  exact lemma_2_3 U T₁ V hU hT₁
