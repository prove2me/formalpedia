-- Prove2me | solution 1 for SoficGroups.ejResidualProjection_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/3f3fba5b-d704-4d05-8678-272c6b204186

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
    [V.HasOrthogonalProjection] (x y : H) :
    inner ℂ (ejResidualProjection V x) y =
      inner ℂ x (ejResidualProjection V y) :=
  Submodule.inner_starProjection_left_eq_right Vᗮ x y
end SoficGroups
