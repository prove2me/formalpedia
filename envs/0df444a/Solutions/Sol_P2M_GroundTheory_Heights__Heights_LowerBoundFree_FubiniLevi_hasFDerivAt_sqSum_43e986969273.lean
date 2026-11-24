-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_hasFDerivAt_sqSum_43e986969273
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:01.317797+00:00
-- url     : https://prove2.me/submissions/47326c5a-2c18-48c4-881b-148a8bde4da8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_apply_5e2c6f879ab5

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
theorem _root_.solution (z : J → ℂ) : HasFDerivAt sqSum ((2 : ℝ) • reInner z) z := by
  have h := HasFDerivAt.sum (u := Finset.univ) (A := fun p (x : J → ℂ) => ‖x p‖ ^ 2)
    fun p _ => (hasFDerivAt_apply p z).norm_sq
  rw [show (∑ p ∈ Finset.univ, fun x : J → ℂ => ‖x p‖ ^ 2) = sqSum from by
    funext x; simp [sqSum, Finset.sum_apply]] at h
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, reInner_apply, Complex.inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring
end GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
