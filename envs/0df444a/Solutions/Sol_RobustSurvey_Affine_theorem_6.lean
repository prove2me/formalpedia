-- Prove2me | solution 1 for RobustSurvey.Affine.theorem_6
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T15:47:21.101483+00:00
-- url     : https://prove2.me/submissions/ea120709-5d86-46d6-9e2a-2ba8ecc387b4

import Definitions.Def_RobustSurvey_Affine_SDP
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix RobustSurvey.Affine

theorem solution : ¬ (∀ {m n₁ n₂ L K : ℕ} (D : Data m n₁ n₂ L)
    (E : Ellipsoids L K) (hK : 0 < K) (ρ : ℝ) (hρ : 0 < ρ),
    ∀ (χ : Decision n₁ n₂ L) (lam : Fin m → Fin K → ℝ),
      sdpFeasible D E ρ χ lam →
        χ ∈ aarcFeasible D E ρ ∧ sdpObjective D χ lam = aarcObjective D χ) := by
  intro h
  let D : Data 1 1 0 1 :=
    { c := 0, b := fun _ => 1, A₁₀ := fun _ _ => 1 / 2, A₁ := fun _ _ _ => 1,
      A₂₀ := 0, A₂ := fun _ => 0 }
  let E : Ellipsoids 1 1 := { S := fun _ => 1, psd := fun _ => Matrix.PosSemidef.one }
  let χ : Decision 1 0 1 := { x := fun _ => 1, q := 0, Q := 0 }
  have hsdp : sdpFeasible D E 1 χ (fun _ _ => 0) := by
    refine ⟨fun _ _ => le_rfl, fun i => ?_⟩
    have hM : certificateMatrix D E 1 χ (fun _ _ => 0) i =
        Matrix.diagonal (Sum.elim (fun _ => 0) (fun _ => (1 / 2 : ℝ))) := by
      ext a b
      rcases a with a | a <;> rcases b with b | b <;>
        simp [certificateMatrix, Matrix.fromBlocks, Gamma, beta, alpha, D, χ, Matrix.mulVec, dotProduct,
          Fin.fin_one_eq_zero] <;> norm_num
    rw [hM]
    apply Matrix.PosSemidef.diagonal
    intro a
    rcases a with a | a <;> norm_num
  have hnot : χ ∉ aarcFeasible D E 1 := by
    intro hχ
    have := hχ (fun _ => 1) (by
      intro k
      simp [E, dotProduct]) 0
    simp [Data.firstMatrix, Data.recourseMatrix, D, χ, Matrix.mulVec, dotProduct] at this
    change (2⁻¹ : ℝ) + (1 : ℝ) • (1 : ℝ) ≤ 1 at this
    norm_num at this
  exact hnot (h D E one_pos 1 one_pos χ (fun _ _ => 0) hsdp).1
