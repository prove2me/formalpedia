-- Prove2me | solution 1 for SoficGroups.ejResidualProjection_re_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/098f7fa7-7159-44bf-81ee-74833ae49973

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejResidualProjection_idempotent
import Theorems.Thm_SoficGroups_ejResidualProjection_inner

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
namespace SoficGroups
theorem _root_.solution (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] (x : H) :
    RCLike.re (inner ℂ (ejResidualProjection V x) x) =
      ‖ejResidualProjection V x‖ ^ 2 := by
  have hinner :
      inner ℂ (ejResidualProjection V x) x =
        inner ℂ (ejResidualProjection V x)
          (ejResidualProjection V x) := by
    calc
      inner ℂ (ejResidualProjection V x) x =
          inner ℂ x (ejResidualProjection V x) :=
        ejResidualProjection_inner V x x
      _ = inner ℂ x
          (ejResidualProjection V (ejResidualProjection V x)) :=
        congrArg (inner ℂ x)
          (ejResidualProjection_idempotent V x).symm
      _ = inner ℂ (ejResidualProjection V x)
          (ejResidualProjection V x) :=
        (ejResidualProjection_inner V x
          (ejResidualProjection V x)).symm
  rw [hinner]
  exact (norm_sq_eq_re_inner _).symm
end SoficGroups
