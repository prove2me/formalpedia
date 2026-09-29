-- Prove2me | solution 1 for SmaleNinth.sub_smul_div_row_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T08:32:20.674186+00:00
-- url     : https://prove2.me/submissions/0b993fe9-a179-4928-a23e-ae14669a9a87

import Definitions.Def_SmaleNinth_GaussJordanPlus
import Theorems.Thm_SmaleNinth_div_row_dotProduct

open Matrix

theorem solution {n : ℕ}
    (u v w : Fin n → ℝ) (a d : ℝ) :
    ((fun k => u k - a * (v k / d)) ⬝ᵥ w) =
      (u ⬝ᵥ w) - a * ((v ⬝ᵥ w) / d) := by
  have hsub :
      (fun k => u k - a * (v k / d)) =
        u - (fun k => a * (v k / d)) := by
    funext k
    simp
  calc
    ((fun k => u k - a * (v k / d)) ⬝ᵥ w) =
        (u ⬝ᵥ w) - ((fun k => a * (v k / d)) ⬝ᵥ w) := by
          rw [hsub, sub_dotProduct]
    _ = (u ⬝ᵥ w) - a * (((fun k => v k / d) ⬝ᵥ w)) := by
      have hscale :
          ((fun k => a * (v k / d)) ⬝ᵥ w) =
            a * (((fun k => v k / d) ⬝ᵥ w)) := by
        change a • (fun k => v k / d) ⬝ᵥ w =
          a • (((fun k => v k / d) ⬝ᵥ w))
        exact smul_dotProduct (R := ℝ) a (fun k => v k / d) w
      exact congrArg (fun t => (u ⬝ᵥ w) - t) hscale
    _ = (u ⬝ᵥ w) - a * ((v ⬝ᵥ w) / d) := by
      rw [SmaleNinth.div_row_dotProduct]
