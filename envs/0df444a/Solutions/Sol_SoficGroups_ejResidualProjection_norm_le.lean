-- Prove2me | solution 1 for SoficGroups.ejResidualProjection_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/ea719241-8ae4-4d5d-bb7e-5e619646fe3c

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
theorem _root_.solution (i : Fin 3) (x : H) :
    ‖ejResidualProjection (V i) x‖ ≤ ‖x‖ :=
  (V i)ᗮ.norm_starProjection_apply_le x
end SoficGroups
