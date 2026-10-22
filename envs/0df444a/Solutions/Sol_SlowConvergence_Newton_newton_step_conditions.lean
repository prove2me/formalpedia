-- Prove2me | solution 1 for SlowConvergence.Newton.newton_step_conditions
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:52:08.944997+00:00
-- url     : https://prove2.me/submissions/879dd7c9-bdbb-442c-b23a-42e5c6f803f1

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

set_option autoImplicit false
open scoped RealInnerProductSpace
open SlowConvergence.Newton

lemma y_eta_pos {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) : 0 < eta τ := by
  unfold eta
  apply div_pos h0; linarith

lemma y_base_le_one (k : ℕ) : 1 / ((k : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma y_mu_pos (τ : ℝ) (k : ℕ) : 0 < mu τ k := by
  unfold mu
  exact Real.rpow_pos_of_pos (by positivity) _

lemma y_mu_le_one {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (k : ℕ) : mu τ k ≤ 1 := by
  unfold mu
  have := y_eta_pos h0 h1
  exact Real.rpow_le_one (by positivity) (y_base_le_one k) (by linarith)

lemma y_mu_sq (τ : ℝ) (k : ℕ) : mu τ k ^ 2 = (1 / ((k : ℝ) + 1)) ^ (1 + 2 * eta τ) := by
  unfold mu
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

lemma y_bk_pos (k : ℕ) : 0 < bk k := by
  unfold bk; positivity

lemma y_Hk_apply (k : ℕ) (v : EuclideanSpace ℝ (Fin 2)) :
    Hk k v = !₂[v 0, bk k * v 1] := by
  ext i
  fin_cases i <;> simp [Hk, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma y_inner2 (u v : EuclideanSpace ℝ (Fin 2)) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    sk τ k = !₂[mu τ k, 1] ∧ 0 < mu τ k ∧ mu τ k ≤ 1 ∧
      ⟪gk τ k, sk τ k⟫ + ⟪Hk k (sk τ k), sk τ k⟫ = 0 ∧
      (∀ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 → 0 < ⟪Hk k v, v⟫) ∧
      Hk k (sk τ k) = -gk τ k ∧
      model τ k (xk τ k + sk τ k) = fk τ (k + 1) := by
  have hsk : sk τ k = !₂[mu τ k, 1] := by
    unfold sk; simp [xk]
  have hb := y_bk_pos k
  have hmu := y_mu_pos τ k
  have hHs : Hk k (sk τ k) = !₂[mu τ k, bk k] := by
    rw [y_Hk_apply, hsk]; simp
  have hgs : gk τ k = -!₂[mu τ k, bk k] := rfl
  refine ⟨hsk, hmu, y_mu_le_one hτ0 hτ1 k, ?_, ?_, ?_, ?_⟩
  · rw [y_inner2, y_inner2, hHs, hsk, hgs]; simp; ring
  · intro v hv
    rw [y_inner2, y_Hk_apply]
    simp
    have h0 : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra h
      push_neg at h
      apply hv
      ext i; fin_cases i <;> simp [h.1, h.2]
    rcases h0 with h | h
    · have := sq_pos_of_ne_zero h
      nlinarith [mul_nonneg hb.le (sq_nonneg (v 1))]
    · have := sq_pos_of_ne_zero h
      nlinarith [mul_pos hb this, sq_nonneg (v 0)]
  · rw [hHs, hgs, neg_neg]
  · have e : xk τ k + sk τ k - xk τ k = sk τ k := by abel
    unfold model
    rw [e, y_inner2, y_inner2, hHs, hsk, hgs]
    show _ = fk τ k - 1 / 2 * ((1 / ((k : ℝ) + 1)) ^ (1 + 2 * eta τ) + (1 / ((k : ℝ) + 1)) ^ 2)
    rw [← y_mu_sq]
    have : bk k = (1 / ((k : ℝ) + 1)) ^ 2 := rfl
    rw [← this]
    simp
    ring
