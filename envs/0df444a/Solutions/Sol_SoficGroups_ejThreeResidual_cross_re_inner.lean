-- Prove2me | solution 1 for SoficGroups.ejThreeResidual_cross_re_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/aad6d79d-6acf-4c8d-bb79-e68077f4bd5f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejResidualProjection_cross_inner

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]
namespace SoficGroups
theorem _root_.solution (x : H) :
    RCLike.re (inner ℂ (ejResidualProjection (V 0) x)
        (ejResidualProjection (V 0) (ejThreeResidualMap V x))) +
      RCLike.re (inner ℂ (ejResidualProjection (V 1) x)
        (ejResidualProjection (V 1) (ejThreeResidualMap V x))) +
      RCLike.re (inner ℂ (ejResidualProjection (V 2) x)
        (ejResidualProjection (V 2) (ejThreeResidualMap V x))) =
      ‖ejThreeResidualMap V x‖ ^ 2 := by
  calc
    _ = RCLike.re (inner ℂ (ejResidualProjection (V 0) x)
          (ejThreeResidualMap V x)) +
        RCLike.re (inner ℂ (ejResidualProjection (V 1) x)
          (ejThreeResidualMap V x)) +
        RCLike.re (inner ℂ (ejResidualProjection (V 2) x)
          (ejThreeResidualMap V x)) := by
      rw [ejResidualProjection_cross_inner (V 0),
        ejResidualProjection_cross_inner (V 1),
        ejResidualProjection_cross_inner (V 2)]
    _ = RCLike.re (inner ℂ
        (ejResidualProjection (V 0) x +
          ejResidualProjection (V 1) x +
          ejResidualProjection (V 2) x)
        (ejThreeResidualMap V x)) := by
      simp only [inner_add_left, map_add]
    _ = ‖ejThreeResidualMap V x‖ ^ 2 := by
      rw [← ejThreeResidualMap_apply V x]
      exact (norm_sq_eq_re_inner _).symm
end SoficGroups
