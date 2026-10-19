-- Prove2me | solution 1 for SoficGroups.ejThreeResidualEnergy_eq_re_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/b9a01e37-02c6-4880-b20b-6f7b095a85ea

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
theorem _root_.solution (x : H) :
    ejThreeResidualEnergy V x =
      RCLike.re (inner ℂ (ejThreeResidualMap V x) x) := by
  simp only [ejThreeResidualEnergy, ejThreeResidualMap_apply,
    inner_add_left, map_add]
  rw [ejResidualProjection_re_inner (V 0) x,
    ejResidualProjection_re_inner (V 1) x,
    ejResidualProjection_re_inner (V 2) x]
end SoficGroups
