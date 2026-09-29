-- Prove2me | solution 1 for WeierstrassCurve.variableChange_mk_smul_eq_self_of_pow_three_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/14646b99-58e5-5b07-927d-49304b9439cb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_pow_three_eq_one

theorem solution
    {R : Type*} [CommRing R] (u : Rˣ) (hu : (u : R) ^ 3 = 1) (B : R) :
    (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve R) =
      ⟨0, 0, 0, 0, B⟩ := by
  have h1 : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h3 : ((u⁻¹ : Rˣ) : R) ^ 3 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 3 = ((u⁻¹ : Rˣ) : R) ^ 3 * (u : R) ^ 3 := by rw [hu, mul_one]
      _ = (((u⁻¹ : Rˣ) : R) * (u : R)) ^ 3 := by ring
      _ = 1 := by rw [h1, one_pow]
  have h6 : ((u⁻¹ : Rˣ) : R) ^ 6 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 6 = (((u⁻¹ : Rˣ) : R) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [h3, one_pow]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
  · ring
  · ring
  · ring
  · ring
  · linear_combination B * h6

end S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_pow_three_eq_one
end P2MW
export P2MW.S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_pow_three_eq_one (solution)
