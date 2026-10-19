-- Prove2me | solution 1 for SoficGroups.ejResidualProjection_cross_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/27da88c6-289a-4d72-b378-4343d6378159

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
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]
namespace SoficGroups
theorem _root_.solution (W : Submodule ℂ H)
    [W.HasOrthogonalProjection] (x z : H) :
    inner ℂ (ejResidualProjection W x) (ejResidualProjection W z) =
      inner ℂ (ejResidualProjection W x) z := by
  calc
    inner ℂ (ejResidualProjection W x) (ejResidualProjection W z) =
        inner ℂ (ejResidualProjection W
          (ejResidualProjection W x)) z :=
      (ejResidualProjection_inner W (ejResidualProjection W x) z).symm
    _ = inner ℂ (ejResidualProjection W x) z := by
      rw [ejResidualProjection_idempotent W x]
end SoficGroups
