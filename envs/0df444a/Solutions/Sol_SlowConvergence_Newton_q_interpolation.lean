-- Prove2me | solution 1 for SlowConvergence.Newton.q_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:02:34.452182+00:00
-- url     : https://prove2.me/submissions/49c37dfe-f694-42dd-a10c-11e946279965

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

open scoped RealInnerProductSpace

namespace Aux_SCNqi

noncomputable def P (A B C D E F : ℝ) (t : ℝ) : ℝ :=
  A + B * t + C * t ^ 2 + D * t ^ 3 + E * t ^ 4 + F * t ^ 5

lemma hasDerivAt_P (A B C D E F t : ℝ) :
    HasDerivAt (P A B C D E F) (P B (2 * C) (3 * D) (4 * E) (5 * F) 0 t) t := by
  have h := ((((((hasDerivAt_const t A).add ((hasDerivAt_id t).const_mul B)).add
    ((hasDerivAt_pow 2 t).const_mul C)).add ((hasDerivAt_pow 3 t).const_mul D)).add
    ((hasDerivAt_pow 4 t).const_mul E)).add ((hasDerivAt_pow 5 t).const_mul F))
  have hf : (P A B C D E F) = (fun x => (fun _ => A) x + B * id x + C * x ^ 2 + D * x ^ 3
      + E * x ^ 4 + F * x ^ 5) := by
    funext x; simp [P]
  rw [hf]
  refine h.congr_deriv ?_
  unfold P
  first
    | ring
    | (norm_num; ring)
    | norm_num

lemma deriv_P (A B C D E F : ℝ) :
    deriv (P A B C D E F) = P B (2 * C) (3 * D) (4 * E) (5 * F) 0 := by
  funext t
  exact (hasDerivAt_P A B C D E F t).deriv

end Aux_SCNqi

open SlowConvergence.Newton Aux_SCNqi in
theorem solution (k : ℕ) :
    q k 0 = 1 / 2 * (1 / ((k : ℝ) + 1)) ^ 2 ∧
      q k 1 = 0 ∧
      deriv (q k) 0 = -((1 / ((k : ℝ) + 1)) ^ 2) ∧
      deriv (q k) 1 = -((1 / ((k : ℝ) + 2)) ^ 2) ∧
      deriv (deriv (q k)) 0 = (1 / ((k : ℝ) + 1)) ^ 2 ∧
      deriv (deriv (q k)) 1 = (1 / ((k : ℝ) + 2)) ^ 2 := by
  have hq : q k = P (1 / 2 * (1 / ((k : ℝ) + 1)) ^ 2) (-((1 / ((k : ℝ) + 1)) ^ 2))
      (1 / 2 * (1 / ((k : ℝ) + 1)) ^ 2)
      (1 / 2 * (9 * (1 / ((k : ℝ) + 2)) ^ 2 - (1 / ((k : ℝ) + 1)) ^ 2))
      (1 / 2 * (-16 * (1 / ((k : ℝ) + 2)) ^ 2 + 2 * (1 / ((k : ℝ) + 1)) ^ 2))
      (1 / 2 * (7 * (1 / ((k : ℝ) + 2)) ^ 2 - (1 / ((k : ℝ) + 1)) ^ 2)) := by
    funext t; unfold q P; ring
  rw [hq, deriv_P, deriv_P]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold P; ring)
