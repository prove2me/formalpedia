-- Prove2me | solution 1 for SoficGroups.ejResidualProjection_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/d37c9bc1-5bc6-4da2-abf9-282e189577e0

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
namespace SoficGroups
theorem _root_.solution (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] (x : H) :
    ejResidualProjection V (ejResidualProjection V x) =
      ejResidualProjection V x := by
  change Vᗮ.starProjection (Vᗮ.starProjection x) = Vᗮ.starProjection x
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem Vᗮ x)
end SoficGroups
