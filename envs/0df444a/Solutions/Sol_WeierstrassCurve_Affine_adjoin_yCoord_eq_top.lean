-- Prove2me | solution 1 for WeierstrassCurve.Affine.adjoin_yCoord_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/987c4a87-b02f-5d37-828f-3c45b69ae14c

import Mathlib
import Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_adjoin_yCoord_eq_top

set_option autoImplicit false

open Polynomial WeierstrassCurve.Affine in
theorem solution {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} :
    IntermediateField.adjoin (RatFunc F) {WeierstrassCurve.Affine.yCoord W} = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  have hpoly : ∀ p : F[X],
      polyToFunctionField W p ∈ IntermediateField.adjoin (RatFunc F) {yCoord W} := by
    intro p
    rw [← algebraMap_polynomial_eq_polyToFunctionField,
      IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField]
    exact IntermediateField.algebraMap_mem _ _
  have hcoord : ∀ r : W.CoordinateRing,
      algebraMap W.CoordinateRing W.FunctionField r
        ∈ IntermediateField.adjoin (RatFunc F) {yCoord W} := by
    intro r
    obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq r
    rw [algebraMap_smul_basis]
    exact add_mem (hpoly p)
      (mul_mem (hpoly q) (IntermediateField.mem_adjoin_simple_self _ _))
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  rw [← hab]
  exact div_mem (hcoord a) (hcoord b)

end S_WeierstrassCurve_Affine_adjoin_yCoord_eq_top
end P2MW
export P2MW.S_WeierstrassCurve_Affine_adjoin_yCoord_eq_top (solution)
