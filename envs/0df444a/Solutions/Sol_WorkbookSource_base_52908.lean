-- Prove2me | solution 1 for WorkbookSource.base_52908
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:58:06.867458+00:00
-- url     : https://prove2.me/submissions/d1820ac2-a0ba-4fdf-8f40-289e9c1f65c6

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
noncomputable section
private def weightPolynomial (a b c d : ℝ) : ℝ :=
  138*(a+b)*(c^3+d^3) + 447*(a+b)*c*d*(c+d)
  + 200*(a^2+b^2)*(c^2+d^2) + 42*(a^2+b^2)*c*d
  + 86*(a^3+b^3)*(c+d) + 8*(a^4+b^4)
  + 396*a*b*(c^2+d^2) + 331*a*b*(a+b)*(c+d)
private def squareCertificate (a b c d : ℝ) : ℝ :=
  (a-b)^2*weightPolynomial a b c d + (a-c)^2*weightPolynomial a c b d
  + (a-d)^2*weightPolynomial a d b c + (b-c)^2*weightPolynomial b c a d
  + (b-d)^2*weightPolynomial b d a c + (c-d)^2*weightPolynomial c d a b
private def homogeneousSum (a b c d : ℝ) : ℝ :=
  a*b*c/(a+b+c+d+d) + b*c*d/(a+b+c+d+a)
  + c*d*a/(a+b+c+d+b) + d*a*b/(a+b+c+d+c)
private lemma homogeneous_bound (a b c d : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) :
    homogeneousSum a b c d ≤ (a+b+c+d)^2/20 := by
  have hpa : 0<a+b+c+d+a := by positivity
  have hpb : 0<a+b+c+d+b := by positivity
  have hpc : 0<a+b+c+d+c := by positivity
  have hpd : 0<a+b+c+d+d := by positivity
  have he : (a+b+c+d)^2/20 - homogeneousSum a b c d = squareCertificate a b c d /
      (240*(a+b+c+d+a)*(a+b+c+d+b)*(a+b+c+d+c)*(a+b+c+d+d)) := by
    unfold homogeneousSum squareCertificate weightPolynomial
    field_simp [ne_of_gt hpa,ne_of_gt hpb,ne_of_gt hpc,ne_of_gt hpd]
    <;> ring
  have hw (p q r s : ℝ) (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s) :
      0 ≤ weightPolynomial p q r s := by unfold weightPolynomial; positivity
  have hn : 0 ≤ squareCertificate a b c d := by
    unfold squareCertificate
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (mul_nonneg (sq_nonneg _) (hw a b c d ha hb hc hd))
      (mul_nonneg (sq_nonneg _) (hw a c b d ha hc hb hd)))
      (mul_nonneg (sq_nonneg _) (hw a d b c ha hd hb hc)))
      (mul_nonneg (sq_nonneg _) (hw b c a d hb hc ha hd)))
      (mul_nonneg (sq_nonneg _) (hw b d a c hb hd ha hc)))
      (mul_nonneg (sq_nonneg _) (hw c d a b hc hd ha hb))
  have hpos : 0 ≤ squareCertificate a b c d /
      (240*(a+b+c+d+a)*(a+b+c+d+b)*(a+b+c+d+c)*(a+b+c+d+d)) := div_nonneg hn (by positivity)
  linarith only [he,hpos]

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a + b + c + d = 4) : (a * b * c) / (d + 4) + (b * c * d) / (a + 4) + (c * d * a) / (b + 4) + (d * a * b) / (c + 4) ≤ 4 / 5   := by
  have h := homogeneous_bound a b c d ha hb hc hd
  simp only [homogeneousSum,habc] at h
  norm_num at h
  simpa only [add_comm (4:ℝ) a,add_comm (4:ℝ) b,add_comm (4:ℝ) c,add_comm (4:ℝ) d] using h

#print axioms solution
