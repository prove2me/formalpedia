-- Prove2me | solution 1 for WorkbookSource.base_9398
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:58:05.907066+00:00
-- url     : https://prove2.me/submissions/08c6ff85-e1b9-4004-a79c-69bcd114e89a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
private lemma inverse_square_pair (u v : ℝ) (hu : 0<u) (hv : 0<v) :
    1/u^2+1/v^2 = ((u+v)^2-2*u*v)/(u*v)^2 := by
  field_simp [ne_of_gt hu,ne_of_gt hv]
  <;> ring
private lemma pair_product_bound (s A B : ℝ) (hA : 0<A) (hB : 0<B) :
    2*(s^2-A-B)/(A*B) ≤ (s^2-2*A)/A^2+(s^2-2*B)/B^2 := by
  have he : (s^2-2*A)/A^2+(s^2-2*B)/B^2-2*(s^2-A-B)/(A*B) =
      s^2*(A-B)^2/(A^2*B^2) := by
    field_simp [ne_of_gt hA,ne_of_gt hB]
    <;> ring
  have hn : 0 ≤ s^2*(A-B)^2/(A^2*B^2) := by positivity
  linarith only [he,hn]

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 1 / (a + b) ^ 2 + 1 / (b + c) ^ 2 + 1 / (c + d) ^ 2 + 1 / (d + a) ^ 2 ≥ 2 / (a * c + b * d)   := by
  let S := a+b+c+d
  let A := (a+b)*(c+d)
  let B := (b+c)*(d+a)
  have hA : 0<A := by dsimp [A]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  have hR : 0<a*c+b*d := by positivity
  have hS1 : (a+b)+(c+d)=S := by dsimp [S]; ring
  have hS2 : (b+c)+(d+a)=S := by dsimp [S]; ring
  have h1 := inverse_square_pair (a+b) (c+d) (by positivity) (by positivity)
  have h2 := inverse_square_pair (b+c) (d+a) (by positivity) (by positivity)
  rw [hS1] at h1
  rw [hS2] at h2
  simp only [mul_assoc] at h1 h2
  change 1/(a+b)^2+1/(c+d)^2 = (S^2-2*A)/A^2 at h1
  change 1/(b+c)^2+1/(d+a)^2 = (S^2-2*B)/B^2 at h2
  have hkey : A*B ≤ (a*c+b*d)*(S^2-A-B) := by
    dsimp [A,B,S]
    nlinarith only [mul_nonneg (le_of_lt (mul_pos ha hc)) (sq_nonneg (a-c)),
      mul_nonneg (le_of_lt (mul_pos hb hd)) (sq_nonneg (b-d)),sq_nonneg (a*c-b*d)]
  have hlo : 2/(a*c+b*d) ≤ 2*(S^2-A-B)/(A*B) := by
    apply (div_le_div_iff₀ hR (mul_pos hA hB)).2
    nlinarith only [hkey]
  have hhi := pair_product_bound S A B hA hB
  calc 2/(a*c+b*d) ≤ 2*(S^2-A-B)/(A*B) := hlo
    _ ≤ (S^2-2*A)/A^2+(S^2-2*B)/B^2 := hhi
    _ = 1/(a+b)^2+1/(b+c)^2+1/(c+d)^2+1/(d+a)^2 := by rw [← h1,← h2]; ring

#print axioms solution
