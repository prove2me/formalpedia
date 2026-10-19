-- Prove2me | solution 1 for SoficGroups.ejResidualProjection_average_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/a9cce981-ae5b-466c-b53e-bc6d99260f3c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_norm_sub_one_third_smul_sq

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
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (x z : H) :
    ‖ejResidualProjection W (x - (3 : ℂ)⁻¹ • z)‖ ^ 2 =
      ‖ejResidualProjection W x‖ ^ 2 -
        (2 / 3 : ℝ) * RCLike.re
          (inner ℂ (ejResidualProjection W x)
            (ejResidualProjection W z)) +
        (1 / 9 : ℝ) * ‖ejResidualProjection W z‖ ^ 2 := by
  rw [map_sub, map_smul]
  exact norm_sub_one_third_smul_sq
    (ejResidualProjection W x) (ejResidualProjection W z)
end SoficGroups
