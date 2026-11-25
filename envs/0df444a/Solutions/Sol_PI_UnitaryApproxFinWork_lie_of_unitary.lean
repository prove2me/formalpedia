-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.lie_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:36.571795+00:00
-- url     : https://prove2.me/submissions/35b76e13-d840-469e-92d1-46fb9d03f616

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Cayley
import Theorems.Thm_PI_UnitaryApproxFinWork_cT_add
import Theorems.Thm_PI_UnitaryApproxFinWork_cT_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.UnitaryApproxFinWork
variable {n : Type} [Fintype n] [DecidableEq n] {A : Type} [CommRing A] (ρ : A →+* A)
namespace PI.UnitaryApproxFinWork
theorem _root_.solution (J g : Matrix n n A) (hg : PI.UnitaryApproxDefs.cT ρ g * J * g = J) (hP : IsUnit (1 + g).det) :
    PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹) = 0 := by
  have hL : PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 + g) = 1 := by
    rw [← PI.UnitaryApproxDefs.cT_mul, Matrix.mul_nonsing_inv _ hP, PI.UnitaryApproxDefs.cT_one]
  have hLinv : PI.UnitaryApproxDefs.cT ρ (1 + g) * PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ = 1 := by
    rw [← PI.UnitaryApproxDefs.cT_mul, Matrix.nonsing_inv_mul _ hP, PI.UnitaryApproxDefs.cT_one]
  have hR : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
  have e1 : (1 - PI.UnitaryApproxDefs.cT ρ g) * J * (1 + g) + (1 + PI.UnitaryApproxDefs.cT ρ g) * J * (1 - g) =
      J + J - (PI.UnitaryApproxDefs.cT ρ g * J * g + PI.UnitaryApproxDefs.cT ρ g * J * g) := by noncomm_ring
  have key : PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)) * (1 + g) = 0 := by
    rw [PI.UnitaryApproxDefs.cT_mul]
    calc PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 - g) * J + J * ((1 - g) * (1 + g)⁻¹)) * (1 + g)
        = (PI.UnitaryApproxDefs.cT ρ (1 + g) * PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹) * PI.UnitaryApproxDefs.cT ρ (1 - g) * J * (1 + g) +
            PI.UnitaryApproxDefs.cT ρ (1 + g) * J * (1 - g) * ((1 + g)⁻¹ * (1 + g)) := by
          simp only [mul_add, add_mul, mul_assoc]
          abel
      _ = PI.UnitaryApproxDefs.cT ρ (1 - g) * J * (1 + g) + PI.UnitaryApproxDefs.cT ρ (1 + g) * J * (1 - g) := by
          rw [hLinv, Matrix.nonsing_inv_mul _ hP, one_mul, mul_one]
      _ = 0 := by
          rw [cT_sub ρ, cT_add ρ, PI.UnitaryApproxDefs.cT_one, e1, hg, sub_self]
  calc PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)
      = PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)) *
          ((1 + g) * (1 + g)⁻¹) := by rw [hL, hR, one_mul, mul_one]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * (PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)) *
          (1 + g)) * (1 + g)⁻¹ := by simp only [mul_assoc]
    _ = 0 := by rw [key, mul_zero, zero_mul]
end PI.UnitaryApproxFinWork
