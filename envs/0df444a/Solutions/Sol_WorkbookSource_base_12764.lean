-- Prove2me | solution 1 for WorkbookSource.base_12764
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:58:07.639629+00:00
-- url     : https://prove2.me/submissions/e44da7fb-0cd3-446a-83c7-d6e720c143e4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
noncomputable section
private def weightAdjacent (a b c d : ℝ) : ℝ :=
  3*(4*a^3*(c+d) + a^2*(13*c^2+32*c*d+16*d^2) + a*b*c*(33*c+8*d)
    + 28*a*c*d^2 + 5*a*d^3 + 12*b*d^3 + 22*c*d^3 + 3*d^4)
private def weightOpposite (a b c d : ℝ) : ℝ :=
  c*(204*a*b*d + 18*a*c*d + 50*b^3 + 144*b^2*d + 120*b*c*d
    + 12*c^2*d + 39*c*d^2 + 7*d^3)
private def squareCertificate (a b c d : ℝ) : ℝ :=
  (a-b)^2*weightAdjacent a b c d + (b-c)^2*weightAdjacent b c d a
  + (c-d)^2*weightAdjacent c d a b + (d-a)^2*weightAdjacent d a b c
  + (a-c)^2*weightOpposite a b c d + (b-d)^2*weightOpposite b c d a
  + (c-a)^2*weightOpposite c d a b + (d-b)^2*weightOpposite d a b c

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a * b * c / (b + c + d) + b * c * d / (c + d + a) + c * d * a / (d + a + b) + d * a * b / (a + b + c)) ≤ (a + b + c + d) ^ 2 / 12   := by
  have hp1 : 0<b+c+d := by positivity
  have hp2 : 0<c+d+a := by positivity
  have hp3 : 0<d+a+b := by positivity
  have hp4 : 0<a+b+c := by positivity
  have he : (a+b+c+d)^2/12 - (a*b*c/(b+c+d)+b*c*d/(c+d+a)+c*d*a/(d+a+b)+d*a*b/(a+b+c))
      = squareCertificate a b c d/(144*(b+c+d)*(c+d+a)*(d+a+b)*(a+b+c)) := by
    unfold squareCertificate weightAdjacent weightOpposite
    field_simp [ne_of_gt hp1,ne_of_gt hp2,ne_of_gt hp3,ne_of_gt hp4]
    <;> ring
  have hn : 0≤squareCertificate a b c d := by
    unfold squareCertificate weightAdjacent weightOpposite
    positivity
  have hpos : 0≤squareCertificate a b c d/(144*(b+c+d)*(c+d+a)*(d+a+b)*(a+b+c)) :=
    div_nonneg hn (by positivity)
  linarith only [he,hpos]

#print axioms solution
