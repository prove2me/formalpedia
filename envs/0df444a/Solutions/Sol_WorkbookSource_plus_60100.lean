-- Prove2me | solution 1 for WorkbookSource.plus_60100
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:49:48.304226+00:00
-- url     : https://prove2.me/submissions/1b276fdf-4661-44f2-84ee-69afc9733bc7

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
noncomputable section
private def cyclicTerm (a b c : ℝ) : ℝ := (a-b)*(a-c)/(a+b)/(a+c)
private def cyclicFour (a b c d : ℝ) : ℝ :=
  cyclicTerm a b c + cyclicTerm b c d + cyclicTerm c d a + cyclicTerm d a b
private def positiveNumerator (c d u v : ℝ) : ℝ :=
  u^2 * (u*((c+2*d)*(v+d)^2+c*d^2) + v^2*(3*c^2+4*c*d+3*d^2+d*v)
    + 2*d*v*(c+d)*(c+2*d) + 2*d^2*(c+d)^2)
  + v^2 * (2*c*(c+d)*(c*(c+d)+u*(2*c+d)+v*(c+u)))
private lemma numerator_nonneg (c d u v : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ positiveNumerator c d u v := by
  unfold positiveNumerator
  positivity
private lemma ordered_cyclic (a b c d : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d)
    (hca : c ≤ a) (hdb : d ≤ b) : 0 ≤ cyclicFour a b c d := by
  have he : cyclicFour a b c d = 2*positiveNumerator c d (a-c) (b-d) /
      ((a+b)*(a+c)*(a+d)*(b+c)*(b+d)*(c+d)) := by
    unfold cyclicFour cyclicTerm positiveNumerator
    simp only [add_comm c a, add_comm d a, add_comm d b]
    field_simp [ne_of_gt (add_pos ha hb),ne_of_gt (add_pos ha hc),
      ne_of_gt (add_pos ha hd),ne_of_gt (add_pos hb hc),
      ne_of_gt (add_pos hb hd),ne_of_gt (add_pos hc hd)]
    <;> ring
  rw [he]
  exact div_nonneg (mul_nonneg (by norm_num) (numerator_nonneg c d (a-c) (b-d)
    (le_of_lt hc) (le_of_lt hd) (sub_nonneg.mpr hca) (sub_nonneg.mpr hdb)))
    (by positivity)
private lemma all_cyclic (a b c d : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) :
    0 ≤ cyclicFour a b c d := by
  rcases le_total c a with hca | hac
  · rcases le_total d b with hdb | hbd
    · exact ordered_cyclic a b c d ha hb hc hd hca hdb
    · have h := ordered_cyclic d a b c hd ha hb hc hbd hca
      have he : cyclicFour a b c d = cyclicFour d a b c := by unfold cyclicFour; ring
      rwa [he]
  · rcases le_total d b with hdb | hbd
    · have h := ordered_cyclic b c d a hb hc hd ha hdb hac
      have he : cyclicFour a b c d = cyclicFour b c d a := by unfold cyclicFour; ring
      rwa [he]
    · have h := ordered_cyclic c d a b hc hd ha hb hac hbd
      have he : cyclicFour a b c d = cyclicFour c d a b := by unfold cyclicFour; ring
      rwa [he]

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a - b) * (a - c) / (a + b) / (a + c) + (-c + b) * (-d + b) / (b + c) / (b + d) + (-d + c) * (-a + c) / (c + d) / (a + c) + (d - a) * (-b + d) / (a + d) / (b + d) ≥ 0    := by
  have h := all_cyclic a b c d ha hb hc hd
  simpa only [cyclicFour, cyclicTerm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

#print axioms solution
