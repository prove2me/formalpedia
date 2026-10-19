-- Prove2me | solution 1 for SoficGroups.ejTwoResidual_sum_re_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/561b0e42-4b79-48c6-89ad-8b2b3afe595e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejResidualProjection_re_inner

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]
namespace SoficGroups
theorem _root_.solution
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (w : H) :
    RCLike.re (inner ℂ
      (ejResidualProjection U w + ejResidualProjection V w) w) =
        ‖ejResidualProjection U w‖ ^ 2 +
          ‖ejResidualProjection V w‖ ^ 2 := by
  have hU :
      (inner ℂ (ejResidualProjection U w) w).re =
        ‖ejResidualProjection U w‖ ^ 2 := by
    change RCLike.re (inner ℂ (ejResidualProjection U w) w) = _
    exact ejResidualProjection_re_inner U w
  have hV :
      (inner ℂ (ejResidualProjection V w) w).re =
        ‖ejResidualProjection V w‖ ^ 2 := by
    change RCLike.re (inner ℂ (ejResidualProjection V w) w) = _
    exact ejResidualProjection_re_inner V w
  change
    (inner ℂ
      (ejResidualProjection U w + ejResidualProjection V w) w).re = _
  simp only [inner_add_left, Complex.add_re]
  rw [hU, hV]
end SoficGroups
