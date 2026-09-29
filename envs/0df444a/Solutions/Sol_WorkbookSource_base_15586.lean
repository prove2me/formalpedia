-- Prove2me | solution 1 for WorkbookSource.base_15586
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:22:17.024283+00:00
-- url     : https://prove2.me/submissions/34a1e187-b831-487d-8289-37883a9beb9f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
private noncomputable def certK (a b : ℝ) : ℝ :=
 (a-b)^2*(182*a*b*(a^3+b^3)+250*a^2*b^2*(a+b))
private noncomputable def certL (a b c d : ℝ) : ℝ :=
 100*(a-b)^2*(c-d)^2*(a*b*(a+b)+c*d*(c+d))
private noncomputable def certM (a b c d : ℝ) : ℝ :=
 (a-b)^2*(a-c)^2*a*(102*d^2+3*(b+c)*d+26*(b^2+c^2)+58*a*d+80*a^2)
 +126*(a^2-b*c)^2*a*b*c
private noncomputable def certT (a b c d : ℝ) : ℝ :=
 certM a b c d+certM b a c d+certM c a b d
private noncomputable def certN (a b c d : ℝ) : ℝ :=
 certK a b+certK a c+certK a d+certK b c+certK b d+certK c d
 +certL a b c d+certL a c b d+certL a d b c
 +certT a b c d+certT a b d c+certT a c d b+certT b c d a
private lemma cert_nonneg (a b c d : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) :
 0 ≤ certN a b c d := by
 unfold certN certT certM certL certK
 positivity
private lemma four_div_nonneg (x y z w A B C D : ℝ)
 (hA : 0<A) (hB : 0<B) (hC : 0<C) (hD : 0<D)
 (h : 0≤x*B*C*D+y*C*D*A+z*D*A*B+w*A*B*C) :
 0≤w/D+x/A+y/B+z/C := by
 have he : w/D+x/A+y/B+z/C = (x*B*C*D+y*C*D*A+z*D*A*B+w*A*B*C)/(A*B*C*D) := by
  field_simp
  <;> ring
 rw [he]
 exact div_nonneg h (by positivity)

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (3 * d - a - b - c) / (2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + d * (a + b + c)) + (3 * a - b - c - d) / (2 * b ^ 2 + 2 * c ^ 2 + 2 * d ^ 2 + a * (b + c + d)) + (3 * b - c - d - a) / (2 * c ^ 2 + 2 * d ^ 2 + 2 * a ^ 2 + b * (a + c + d)) + (3 * c - d - a - b) / (2 * d ^ 2 + 2 * a ^ 2 + 2 * b ^ 2 + c * (d + a + b)) ≥ 0   := by
  let A := 2*b^2+2*c^2+2*d^2+a*(b+c+d)
  let B := 2*c^2+2*d^2+2*a^2+b*(a+c+d)
  let C := 2*d^2+2*a^2+2*b^2+c*(d+a+b)
  let D := 2*a^2+2*b^2+2*c^2+d*(a+b+c)
  have hA : 0<A := by dsimp [A]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  have he : 10*((3*a-b-c-d)*B*C*D+(3*b-c-d-a)*C*D*A+
      (3*c-d-a-b)*D*A*B+(3*d-a-b-c)*A*B*C) = certN a b c d := by
    dsimp [A,B,C,D,certN,certT,certM,certL,certK]
    ring
  have hn := cert_nonneg a b c d ha hb hc hd
  have hp : 0≤(3*a-b-c-d)*B*C*D+(3*b-c-d-a)*C*D*A+
      (3*c-d-a-b)*D*A*B+(3*d-a-b-c)*A*B*C := by
    linarith only [he,hn]
  exact four_div_nonneg _ _ _ _ A B C D hA hB hC hD hp

#print axioms solution
