-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P09.circleAutomorphism_reduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:55:28.014133+00:00
-- url     : https://prove2.me/submissions/65294785-69ea-499f-a173-0ef205dc779a

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P09

open scoped Manifold ContDiff
open QAlgorithms.Papers.Independent.Bridge50.P09

theorem solution :
    actionCommutatorSubgroup circleAutomorphismAction = ⊤ ∧
      Nonempty ((Circle ⧸ actionCommutatorSubgroup circleAutomorphismAction) ≃* PUnit) := by
  have htop : actionCommutatorSubgroup circleAutomorphismAction = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨t, rfl⟩ := Circle.exp_surjective z
    have hz : Circle.exp t = (Circle.exp (-(t/2)))⁻¹ * circleAutomorphismAction 1 (Circle.exp (-(t/2))) := by
      simp only [circleAutomorphismAction, one_ne_zero, if_false]
      rw [← Circle.exp_neg, ← Circle.exp_add]
      congr 1; ring
    rw [hz]
    exact Subgroup.subset_closure ⟨1, _, rfl⟩
  refine ⟨htop, ⟨?_⟩⟩
  haveI : Subsingleton (Circle ⧸ actionCommutatorSubgroup circleAutomorphismAction) := by
    rw [htop]; exact QuotientGroup.subsingleton_quotient_top
  exact { toFun := fun _ => PUnit.unit, invFun := fun _ => 1,
          left_inv := fun _ => Subsingleton.elim _ _, right_inv := fun _ => rfl,
          map_mul' := fun _ _ => rfl }
