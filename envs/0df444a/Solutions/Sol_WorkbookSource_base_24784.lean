-- Prove2me | solution 1 for WorkbookSource.base_24784
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:04:46.79233+00:00
-- url     : https://prove2.me/submissions/d622e10b-9f2e-4546-896a-e64f4fe9686d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution (a b c d : ℝ) (h : a + b + c + d = 4) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 1 / (a * b) + 1 / (b * c) + 1 / (c * d) + 1 / (d * a) ≥ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2   := by
  have he : (a+b+c+d)^4*(a+c)*(b+d)-256*(a*b*c*d)*(a^2+b^2+c^2+d^2) =
      (a+c)*(b+d)*(a+c-b-d)^4 + 8*(b+d)^4*(a-c)^2 + 8*(a+c)^4*(b-d)^2
      + 32*b*d*(a-c)^4 + 32*a*c*(b-d)^4 := by ring
  have hp : 0 ≤ (a+c)*(b+d)*(a+c-b-d)^4 + 8*(b+d)^4*(a-c)^2 + 8*(a+c)^4*(b-d)^2
      + 32*b*d*(a-c)^4 + 32*a*c*(b-d)^4 := by positivity
  rw [h] at he
  norm_num at he
  have hn : (a^2+b^2+c^2+d^2)*(a*b*c*d) ≤ (a+c)*(b+d) := by
    nlinarith only [he,hp]
  have hrat : 1/(a*b)+1/(b*c)+1/(c*d)+1/(d*a) = (a+c)*(b+d)/(a*b*c*d) := by
    field_simp [ne_of_gt ha,ne_of_gt hb,ne_of_gt hc,ne_of_gt hd]
    <;> ring
  rw [hrat]
  exact (le_div_iff₀ (show 0<a*b*c*d by positivity)).2 hn

#print axioms solution
