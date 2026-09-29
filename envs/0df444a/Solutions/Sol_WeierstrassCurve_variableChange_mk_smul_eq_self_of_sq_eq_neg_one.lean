-- Prove2me | solution 1 for WeierstrassCurve.variableChange_mk_smul_eq_self_of_sq_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6f7ccc40-1684-5b0c-9690-8d627da65aae

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_sq_eq_neg_one

theorem solution
    {R : Type*} [CommRing R] (u : Rˣ) (hu : (u : R) ^ 2 = -1) (A : R) :
    (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve R) =
      ⟨0, 0, 0, A, 0⟩ := by
  have h1 : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hu4 : (u : R) ^ 4 = 1 := by
    calc (u : R) ^ 4 = ((u : R) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hu]; ring
  have h4 : ((u⁻¹ : Rˣ) : R) ^ 4 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 4 = ((u⁻¹ : Rˣ) : R) ^ 4 * (u : R) ^ 4 := by rw [hu4, mul_one]
      _ = (((u⁻¹ : Rˣ) : R) * (u : R)) ^ 4 := by ring
      _ = 1 := by rw [h1, one_pow]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
  · ring
  · ring
  · ring
  · linear_combination A * h4
  · ring

end S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_sq_eq_neg_one
end P2MW
export P2MW.S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_sq_eq_neg_one (solution)
