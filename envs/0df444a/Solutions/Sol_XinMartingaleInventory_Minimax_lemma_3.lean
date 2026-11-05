-- Prove2me | solution 1 for XinMartingaleInventory.Minimax.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-04T12:28:53.27338+00:00
-- url     : https://prove2.me/submissions/dbcc1f8a-cd4f-40cf-9daf-2dea347fae2c

import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

open Set

theorem solution (a c : ℝ) (f D : ℝ → ℝ)
    (hcont : ContinuousOn f (Set.Ioo a c))
    (hderiv : ∀ x ∈ Set.Ioo a c, HasDerivWithinAt f (D x) (Set.Ioi x) x)
    (hmono : MonotoneOn D (Set.Ioo a c)) : ConvexOn ℝ (Set.Ioo a c) f := by
  refine convexOn_of_slope_mono_adjacent (convex_Ioo a c) ?_
  intro x y z hx hz hxy hyz
  have hy : y ∈ Ioo a c := ⟨lt_trans hx.1 hxy, lt_trans hyz hz.2⟩
  have hxyI : Icc x y ⊆ Ioo a c := by intro t ht; exact ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  have hyzI : Icc y z ⊆ Ioo a c := by intro t ht; exact ⟨lt_of_lt_of_le hy.1 ht.1, lt_of_le_of_lt ht.2 hz.2⟩
  have hup : f y ≤ f x + D y * (y - x) := by
    apply image_le_of_deriv_right_le_deriv_boundary (hcont.mono hxyI)
      (fun t ht => (hderiv t (hxyI ⟨ht.1, ht.2.le⟩)).Ici_of_Ioi)
      (B := fun t => f x + D y * (t - x)) (B' := fun _ => D y)
      (by simp) (by fun_prop)
      (fun t _ => by simpa using (((hasDerivAt_id t).sub_const x).const_mul (D y)).const_add (f x) |>.hasDerivWithinAt)
      (fun t ht => hmono (hxyI ⟨ht.1, ht.2.le⟩) hy ht.2.le)
      (right_mem_Icc.mpr hxy.le)
  have hlo : -f z ≤ -f y - D y * (z - y) := by
    apply image_le_of_deriv_right_le_deriv_boundary (hcont.neg.mono hyzI)
      (fun t ht => (hderiv t (hyzI ⟨ht.1, ht.2.le⟩)).Ici_of_Ioi.neg)
      (B := fun t => -f y - D y * (t - y)) (B' := fun _ => -D y)
      (by simp) (by fun_prop)
      (fun t _ => by simpa [sub_eq_add_neg] using
        ((((hasDerivAt_id t).sub_const y).const_mul (D y)).neg.const_add (-f y)).hasDerivWithinAt)
      (fun t ht => neg_le_neg (hmono hy (hyzI ⟨ht.1, ht.2.le⟩) ht.1))
      (right_mem_Icc.mpr hyz.le)
  apply le_trans ((div_le_iff₀ (sub_pos.mpr hxy)).mpr (by linarith : f y - f x ≤ D y * (y - x)))
  apply (le_div_iff₀ (sub_pos.mpr hyz)).mpr
  linarith

#print axioms solution
