-- Prove2me | solution 1 for SoficGroups.ejThreeResidualEnergy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/d8f6ea86-4892-493b-8a4a-c7d53397ae07

import Mathlib
import Definitions.Def_NonSoficGroup

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
    0 ≤ ejThreeResidualEnergy V x := by
  unfold ejThreeResidualEnergy
  positivity
end SoficGroups
