-- Prove2me | solution 1 for classical_markov_range
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-09T07:32:00.004353+00:00
-- url     : https://prove2.me/submissions/b0875906-c30b-44d6-9d22-a6db13c06b58
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_markov_unit
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

open Polynomial Set

namespace CMRSketch

/-- A polynomial equal to the constant `m` on an infinite interval is `C m`. -/
lemma eq_C_of_const_on_Icc {Q : Polynomial ℝ} {a b m : ℝ} (hab : a < b)
    (h : ∀ x : ℝ, a ≤ x → x ≤ b → Q.eval x = m) : Q = C m := by
  have hsub : ∀ x ∈ Set.Icc a b, (Q - C m).IsRoot x := by
    intro x hx
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C, h x hx.1 hx.2, sub_self]
  have hIcc_inf : (Set.Icc a b).Infinite := Set.infinite_coe_iff.mp (Set.Icc.infinite hab)
  have hinf : Set.Infinite {x | (Q - C m).IsRoot x} := hIcc_inf.mono hsub
  have h0 := Polynomial.eq_zero_of_infinite_isRoot (Q - C m) hinf
  exact sub_eq_zero.mp h0

end CMRSketch

open CMRSketch

/-- Sketch: reduce `classical_markov_range` on `[a,b]` with bounds `m ≤ Q ≤ M`
to `markov_unit` (the `[-1,1]`, `|Q| ≤ 1` form). If `m = M`, `Q` is constant so `Q' = 0`.
Otherwise affine-rescale `P(u) := (2 Q((b-a)(u+1)/2 + a) - M - m)/(M - m)` and apply
`markov_unit` to `P`. -/
theorem solution
    (a b : ℝ) (hab : a < b) (Q : Polynomial ℝ) {d : ℕ} (hd : Q.natDegree ≤ d)
    (m M : ℝ)
    (hm : ∀ x : ℝ, a ≤ x → x ≤ b → m ≤ Q.eval x)
    (hM : ∀ x : ℝ, a ≤ x → x ≤ b → Q.eval x ≤ M) :
    ∀ c : ℝ, a ≤ c → c ≤ b → |Q.derivative.eval c| ≤ (d : ℝ)^2 * (M - m) / (b - a) := by
  intro c hca hcb
  have hba : (0 : ℝ) < b - a := by linarith
  have hmM : m ≤ M := (hm a le_rfl hab.le).trans (hM a le_rfl hab.le)
  rcases eq_or_lt_of_le hmM with hmM_eq | hmM_lt
  · -- Degenerate: m = M, Q is constant on [a,b].
    subst hmM_eq
    have hQc : Q = C m := eq_C_of_const_on_Icc hab (fun x hx1 hx2 => le_antisymm (hM x hx1 hx2) (hm x hx1 hx2))
    rw [hQc, Polynomial.derivative_C, Polynomial.eval_zero, abs_zero, sub_self, mul_zero, zero_div]
  · -- Nondegenerate: m < M.
    set α := (b - a) / 2 with hα_def
    set β := (a + b) / 2 with hβ_def
    have hα_pos : (0 : ℝ) < α := by rw [hα_def]; linarith
    have hMm : (0 : ℝ) < M - m := by linarith
    -- The affine polynomial L(u) = α u + β.
    set L : Polynomial ℝ := C α * X + C β with hL_def
    -- The rescaled polynomial P := (2/(M-m)) * Q.comp L - (M+m)/(M-m).
    set P : Polynomial ℝ := C (2 / (M - m)) * Q.comp L - C ((M + m) / (M - m)) with hP_def
    -- 1. L evaluates as an affine map.
    have hL_eval : ∀ u : ℝ, L.eval u = α * u + β := by
      intro u; rw [hL_def]; simp
    -- 2. For u ∈ [-1,1], L(u) ∈ [a,b].
    have hL_mem : ∀ u : ℝ, -1 ≤ u → u ≤ 1 → a ≤ L.eval u ∧ L.eval u ≤ b := by
      intro u hu1 hu2
      rw [hL_eval]
      constructor
      · rw [hα_def, hβ_def]; nlinarith
      · rw [hα_def, hβ_def]; nlinarith
    -- 3. P evaluates as the affine rescale of Q.
    have hP_eval : ∀ u : ℝ, P.eval u = (2 * Q.eval (α * u + β) - M - m) / (M - m) := by
      intro u
      rw [hP_def]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        hL_eval u]
      ring
    -- 4. |P| ≤ 1 on [-1,1].
    have hP_bound : ∀ u : ℝ, -1 ≤ u → u ≤ 1 → |P.eval u| ≤ 1 := by
      intro u hu1 hu2
      obtain ⟨hmem1, hmem2⟩ := hL_mem u hu1 hu2
      rw [hL_eval] at hmem1 hmem2
      have h_lo := hm (α * u + β) hmem1 hmem2
      have h_hi := hM (α * u + β) hmem1 hmem2
      rw [hP_eval, abs_le]
      constructor
      · rw [le_div_iff₀ hMm]; nlinarith
      · rw [div_le_iff₀ hMm]; nlinarith
    -- 5. deg P ≤ d.
    have hL_deg : L.natDegree = 1 := by
      rw [hL_def]
      compute_degree!
      exact ne_of_gt hα_pos
    have hP_deg : P.natDegree ≤ d := by
      have h1 : (Q.comp L).natDegree = Q.natDegree * L.natDegree := Polynomial.natDegree_comp
      rw [hL_deg, mul_one] at h1
      calc P.natDegree = (C (2 / (M - m)) * Q.comp L - C ((M + m) / (M - m))).natDegree := by rw [hP_def]
        _ ≤ max (C (2 / (M - m)) * Q.comp L).natDegree (C ((M + m) / (M - m))).natDegree :=
            Polynomial.natDegree_sub_le _ _
        _ = (C (2 / (M - m)) * Q.comp L).natDegree := by rw [Polynomial.natDegree_C]; exact Nat.max_eq_left (Nat.zero_le _)
        _ ≤ (Q.comp L).natDegree := Polynomial.natDegree_C_mul_le _ _
        _ = Q.natDegree := h1
        _ ≤ d := hd
    -- 6. Derivative of P.
    have hL_deriv : derivative L = C α := by rw [hL_def]; simp
    have hP_deriv : ∀ u : ℝ, P.derivative.eval u = (b - a) / (M - m) * Q.derivative.eval (α * u + β) := by
      intro u
      rw [hP_def]
      simp only [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero,
        Polynomial.derivative_C_mul, Polynomial.derivative_comp, hL_deriv,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, hL_eval u]
      rw [hα_def]; ring
    -- 7. Apply markov_unit to P.
    have hmarkov := markov_unit P hP_deg hP_bound
    -- 8. Instantiate at u := (2c - a - b)/(b - a).
    set u := (2 * c - a - b) / (b - a) with hu_def
    have hu1 : -1 ≤ u := by rw [hu_def]; rw [le_div_iff₀ hba]; linarith
    have hu2 : u ≤ 1 := by rw [hu_def]; rw [div_le_iff₀ hba]; linarith
    have hcu : α * u + β = c := by rw [hα_def, hβ_def, hu_def]; field_simp; ring
    have := hmarkov u hu1 hu2
    rw [hP_deriv u, hcu, abs_mul, abs_div] at this
    have hba_abs : |b - a| = b - a := abs_of_pos hba
    have hMm_abs : |M - m| = M - m := abs_of_pos hMm
    rw [hba_abs, hMm_abs] at this
    -- this : (b-a)/(M-m) * |Q'(c)| ≤ d²
    -- want : |Q'(c)| ≤ d²(M-m)/(b-a)
    rw [le_div_iff₀ hba]
    have key : |Q.derivative.eval c| * (b - a) = (M - m) * ((b - a) / (M - m) * |Q.derivative.eval c|) := by
      field_simp
    rw [key]
    calc (M - m) * ((b - a) / (M - m) * |Q.derivative.eval c|)
        ≤ (M - m) * (↑d ^ 2) := mul_le_mul_of_nonneg_left this (le_of_lt hMm)
      _ = ↑d ^ 2 * (M - m) := by ring
