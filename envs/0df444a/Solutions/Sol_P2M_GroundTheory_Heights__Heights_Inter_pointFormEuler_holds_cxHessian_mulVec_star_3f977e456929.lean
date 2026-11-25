-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_cxHessian_mulVec_star_3f977e456929
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:34:50.502629+00:00
-- url     : https://prove2.me/submissions/171bcb48-4779-4ecd-9056-9f24b6f3aa47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_add_right_4973c981d991
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_real_smul_right_41833679cb9c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_I_smul_right_1b7eb63621a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_sum_right_ebed156926f6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
theorem _root_.solution (f : (Fin n → ℂ) → ℝ) (y x : Fin n → ℂ) (i : Fin n) :
    (cxHessian f y *ᵥ star x) i = leviOf (fderiv ℝ (fderiv ℝ f) y) (Pi.single i 1) x := by
  set H := fderiv ℝ (fderiv ℝ f) y
  have hx : x = ∑ j, ((x j).re • (Pi.single j 1 : Fin n → ℂ) +
      (x j).im • (Complex.I • (Pi.single j 1 : Fin n → ℂ))) := by
    funext p
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Complex.real_smul, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    conv_lhs => rw [← Complex.re_add_im (x p)]
  have hent : ∀ j, cxHessian f y i j = leviOf H (Pi.single i 1) (Pi.single j 1) := fun j => rfl
  conv_rhs => rw [hx]
  rw [leviOf_sum_right]
  simp only [mulVec, dotProduct, hent]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [leviOf_add_right, leviOf_real_smul_right, leviOf_real_smul_right, leviOf_I_smul_right]
  have hs : star (x j) = ((x j).re : ℂ) - (x j).im * Complex.I := by
    apply Complex.ext <;> simp
  simp only [Pi.star_apply, hs]
  ring
end GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
