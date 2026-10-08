-- Prove2me | solution 1 for SuttonBartoRL.Traces.lms_weights_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:30:04.13627+00:00
-- url     : https://prove2.me/submissions/69826b34-48e8-48c9-a1e6-3b1341cf36c5

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_DutchMC

open Matrix in
theorem lmsW77465b09_step {d : ℕ} (α G : ℝ) (x : ℕ → Fin d → ℝ) (w₀ : Fin d → ℝ) (t : ℕ) :
    SuttonBartoRL.Traces.lmsWeights α G x w₀ (t + 1) =
      SuttonBartoRL.Traces.fadingMatrix α x t *ᵥ SuttonBartoRL.Traces.lmsWeights α G x w₀ t
        + (α * G) • x t := by
  funext i
  simp only [SuttonBartoRL.Traces.lmsWeights, SuttonBartoRL.Traces.fadingMatrix,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  rw [dotProduct_comm]
  ring

open Matrix in
theorem fadeProd77465b09_succ {d : ℕ} (α : ℝ) (x : ℕ → Fin d → ℝ) (j t : ℕ) (h : j ≤ t + 1) :
    SuttonBartoRL.Traces.fadeProd α x j (t + 1) =
      SuttonBartoRL.Traces.fadingMatrix α x (t + 1) * SuttonBartoRL.Traces.fadeProd α x j t := by
  rw [SuttonBartoRL.Traces.fadeProd, if_pos h]

open Matrix in
theorem fadeProd77465b09_empty {d : ℕ} (α : ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ) :
    SuttonBartoRL.Traces.fadeProd α x (t + 1) t = 1 := by
  cases t with
  | zero => simp [SuttonBartoRL.Traces.fadeProd]
  | succ n => rw [SuttonBartoRL.Traces.fadeProd, if_neg (by omega)]

open Matrix in
theorem lmsW77465b09_closed {d : ℕ} (α G : ℝ) (x : ℕ → Fin d → ℝ) (w₀ : Fin d → ℝ) (T : ℕ) :
    SuttonBartoRL.Traces.lmsWeights α G x w₀ (T + 1) =
      SuttonBartoRL.Traces.fadeProd α x 0 T *ᵥ w₀ +
        (α * G) • ∑ k ∈ Finset.range (T + 1), SuttonBartoRL.Traces.fadeProd α x (k + 1) T *ᵥ x k := by
  induction T with
  | zero =>
    rw [lmsW77465b09_step, Finset.sum_range_one, fadeProd77465b09_empty, Matrix.one_mulVec]
    simp [SuttonBartoRL.Traces.lmsWeights, SuttonBartoRL.Traces.fadeProd]
  | succ n ih =>
    rw [lmsW77465b09_step, ih, Finset.sum_range_succ _ (n + 1), fadeProd77465b09_empty,
      Matrix.one_mulVec, fadeProd77465b09_succ α x 0 n (by omega), Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_sum, Matrix.mulVec_mulVec]
    have hs : ∀ k ∈ Finset.range (n + 1),
        SuttonBartoRL.Traces.fadingMatrix α x (n + 1) *ᵥ
          SuttonBartoRL.Traces.fadeProd α x (k + 1) n *ᵥ x k =
        SuttonBartoRL.Traces.fadeProd α x (k + 1) (n + 1) *ᵥ x k := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [fadeProd77465b09_succ α x (k + 1) n (by omega), Matrix.mulVec_mulVec]
    rw [Finset.sum_congr rfl hs, smul_add]
    abel

open Matrix in
theorem solution {d : ℕ} (α G : ℝ) (x : ℕ → Fin d → ℝ) (w₀ : Fin d → ℝ)
    (T : ℕ) (hT : 1 ≤ T) :
    SuttonBartoRL.Traces.lmsWeights α G x w₀ T =
      SuttonBartoRL.Traces.fadeProd α x 0 (T - 1) *ᵥ w₀ +
        (α * G) • ∑ k ∈ Finset.range T, SuttonBartoRL.Traces.fadeProd α x (k + 1) (T - 1) *ᵥ x k := by
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  simpa using lmsW77465b09_closed α G x w₀ n
