-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KTheta_integral_exp_sum_sq_107f6dbe98ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:01:11.170604+00:00
-- url     : https://prove2.me/submissions/f76bec9a-2cc5-417c-a80f-985d9861beb3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix MeasureTheory Real
open scoped MatrixOrder
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KTheta
noncomputable section
variable {g : ℕ}
namespace GroundTheory.Heights₂.Heights.KTheta
theorem _root_.solution (c : ℝ) :
    ∫ x : Fin g → ℝ, exp (-c * ∑ i, x i ^ 2) = (√(π / c)) ^ g := by
  have h : (fun x : Fin g → ℝ => exp (-c * ∑ i, x i ^ 2)) = fun x => ∏ i, exp (-c * x i ^ 2) := by
    funext x; rw [Finset.mul_sum, Real.exp_sum]
  rw [h, integral_fintype_prod_volume_eq_prod (f := fun _ (t : ℝ) => exp (-c * t ^ 2))]
  simp only [integral_gaussian, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end GroundTheory.Heights₂.Heights.KTheta
