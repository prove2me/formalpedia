-- Prove2me | solution 1 for YeIPA.QPApprox.qp_min_arcsin_infimum
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T22:24:02.681699+00:00
-- url     : https://prove2.me/submissions/fbf40eae-7742-4d25-bcff-167863aca35f

import Mathlib
import Definitions.Def_YeIPA_QPApprox_Relaxation

open Matrix MeasureTheory

open YeIPA.QPApprox in
theorem solution :
    ¬ (∀ {m n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
      (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hfeas : ∃ x, IsQPFeasible A b x),
      IsGLB {t : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ,
          (∀ i, frob (constrMat A i) X = b i) ∧ (∀ j, diagVec X j ≤ 1) ∧ X.PosDef ∧
          t = (2 / Real.pi) * frob Q (arcsinTransform X)}
        (qpMin Q A b)) := by
  intro h
  have hfeas : ∃ x, IsQPFeasible (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 x :=
    ⟨0, fun i => by simp, fun j => by norm_num⟩
  have H := h (m := 1) (n := 1) 0 (by simp [Matrix.IsSymm]) 1 0 hfeas
  have hempty : {t : ℝ | ∃ X : Matrix (Fin 1) (Fin 1) ℝ,
      (∀ i, frob (constrMat (1 : Matrix (Fin 1) (Fin 1) ℝ) i) X = (0 : Fin 1 → ℝ) i) ∧
        (∀ j, diagVec X j ≤ 1) ∧ X.PosDef ∧
        t = (2 / Real.pi) * frob 0 (arcsinTransform X)} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro X hc _ hpd _
    have h0 := hc 0
    simp [frob, constrMat] at h0
    have := hpd.diag_pos (i := 0)
    linarith
  rw [hempty] at H
  have := H.2 (show qpMin (0 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 + 1 ∈ lowerBounds (∅ : Set ℝ) by simp)
  linarith
