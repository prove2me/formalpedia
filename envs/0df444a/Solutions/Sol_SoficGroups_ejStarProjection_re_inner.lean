-- Prove2me | solution 1 for SoficGroups.ejStarProjection_re_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/a4223ed3-5c7a-46a2-8899-c133baef51ea

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
namespace SoficGroups
theorem _root_.solution (W : Submodule ℂ H)
    [W.HasOrthogonalProjection] (x : H) :
    RCLike.re (inner ℂ (W.starProjection x) x) =
      ‖W.starProjection x‖ ^ 2 := by
  have hidem : W.starProjection (W.starProjection x) =
      W.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr
      (Submodule.starProjection_apply_mem W x)
  have hinner :
      inner ℂ (W.starProjection x) x =
        inner ℂ (W.starProjection x) (W.starProjection x) := by
    calc
      inner ℂ (W.starProjection x) x =
          inner ℂ x (W.starProjection x) :=
        Submodule.inner_starProjection_left_eq_right W x x
      _ = inner ℂ x (W.starProjection (W.starProjection x)) :=
        congrArg (inner ℂ x) hidem.symm
      _ = inner ℂ (W.starProjection x) (W.starProjection x) :=
        (Submodule.inner_starProjection_left_eq_right W x
          (W.starProjection x)).symm
  rw [hinner]
  exact (norm_sq_eq_re_inner _).symm
end SoficGroups
