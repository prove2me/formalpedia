-- Prove2me | solution 1 for SoficGroups.ejStarProjection_mem_inf_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/8b952cef-ca63-43a1-ab11-73178b1ead9e

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
theorem _root_.solution
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    (w : H) (hw : w ∈ (U ⊓ V)ᗮ) :
    U.starProjection w ∈ (U ⊓ V)ᗮ := by
  intro q hq
  calc
    inner ℂ q (U.starProjection w) =
        inner ℂ (U.starProjection q) w :=
      (Submodule.inner_starProjection_left_eq_right U q w).symm
    _ = inner ℂ q w := by
      rw [Submodule.starProjection_eq_self_iff.mpr hq.1]
    _ = 0 := hw q hq
end SoficGroups
