-- Prove2me | solution 1 for SoficGroups.norm_sub_one_third_smul_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/f4c19677-b1ac-4f00-ba6d-2a34d8af8382

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
theorem _root_.solution (a b : H) :
    ‖a - (3 : ℂ)⁻¹ • b‖ ^ 2 =
      ‖a‖ ^ 2 - (2 / 3 : ℝ) * RCLike.re (inner ℂ a b) +
        (1 / 9 : ℝ) * ‖b‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
  norm_num [Complex.mul_re]
  ring
end SoficGroups
