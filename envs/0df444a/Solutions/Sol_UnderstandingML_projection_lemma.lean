-- Prove2me | solution 1 for UnderstandingML.projection_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T17:37:43.478467+00:00
-- url     : https://prove2.me/submissions/1bc15efa-8da0-406e-aa9b-1fa965ccc2d9

import Definitions.Def_UnderstandingML_SGD

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

theorem solution {d : ℕ} (H : Set (Vec d)) (hH : Convex ℝ H) (w v : Vec d)
    (hv : IsProjection H w v) (u : Vec d) (hu : u ∈ H) :
    0 ≤ ‖w - u‖ ^ 2 - ‖v - u‖ ^ 2 := by
  obtain ⟨hvH, hmin⟩ := hv
  have hinf : ‖w - v‖ = ⨅ x : H, ‖w - (x : Vec d)‖ := by
    have : Nonempty H := ⟨⟨v, hvH⟩⟩
    have hbdd : BddBelow (Set.range fun x : H => ‖w - (x : Vec d)‖) :=
      ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
    refine le_antisymm (le_ciInf fun x => ?_) ?_
    · rw [norm_sub_rev w v, norm_sub_rev w (x : Vec d)]; exact hmin x x.2
    · exact ciInf_le hbdd (⟨v, hvH⟩ : H)
  have key := (norm_eq_iInf_iff_real_inner_le_zero hH hvH).1 hinf u hu
  have e : w - u = (w - v) + (v - u) := by abel
  rw [e, @norm_add_sq_real]
  have : ⟪w - v, v - u⟫_ℝ = -⟪w - v, u - v⟫_ℝ := by
    rw [← inner_neg_right, neg_sub]
  nlinarith [norm_nonneg (w - v), sq_nonneg ‖w - v‖]
