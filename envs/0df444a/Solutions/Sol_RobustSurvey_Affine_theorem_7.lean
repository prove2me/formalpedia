-- Prove2me | solution 1 for RobustSurvey.Affine.theorem_7
-- status  : ACCEPTED   (disprove)
-- author  : @frknbls
-- created : 2026-11-04T13:48:40.910238+00:00
-- url     : https://prove2.me/submissions/0c0196ae-8e6f-466b-b523-f142e27783ef

import Definitions.Def_RobustSurvey_Affine_SDP
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank

open Matrix

namespace RobustSurvey.Affine

theorem _root_.solution : ¬ (∀ {m n₁ n₂ L K : ℕ} (D : Data m n₁ n₂ L)
    (E : Ellipsoids L K) (hrank : 0 < E.rankSum) (ρ : ℝ) (hρ : 0 < ρ),
    aarcFeasible D E (E.gamma * ρ) ⊆ approxFeasible D E ρ ∧
      approxFeasible D E ρ ⊆ aarcFeasible D E ρ) := by
  intro h
  let D : Data 1 1 0 1 :=
    { c := 0, b := fun _ => 1, A₁₀ := fun _ _ => 1 / 2, A₁ := fun _ _ _ => 1,
      A₂₀ := 0, A₂ := fun _ => 0 }
  let E : Ellipsoids 1 1 := { S := fun _ => 1, psd := fun _ => Matrix.PosSemidef.one }
  have hrank : 0 < E.rankSum := by
    simp [Ellipsoids.rankSum, E, Matrix.rank_one]
  let χ : Decision 1 0 1 := { x := fun _ => 1, q := 0, Q := 0 }
  have happrox : χ ∈ approxFeasible D E 1 := by
    refine ⟨fun _ _ => 0, fun _ _ => le_rfl, fun i => ?_⟩
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
  exact hnot ((h D E hrank 1 one_pos).2 happrox)

end RobustSurvey.Affine
