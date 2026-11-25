-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_integral_det_fderiv_eq_zero_65eb4a12eacd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:47:04.907326+00:00
-- url     : https://prove2.me/submissions/6ca9268b-2770-4f53-8604-023fad51e4c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChangeOfVariablesDegreePiola
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_det_fderiv_eq_det_jacobian_2f5e8fc08a22
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_jacobian_eq_fderiv_apply_78ebb9abef90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_det_update_eq_sum_10ad24af5154
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_sum_fderiv_cofactorFn_eq_zero_8bc35bb39030
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ChangeOfVariablesDegree_contDiff_cofactorFn_aded9930e4f5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped ContDiff
open MeasureTheory
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
theorem _root_.solution (H : (Fin n → ℝ) → Fin n → ℝ) (hH : ContDiff ℝ ∞ H)
    (i : Fin n) (hi : HasCompactSupport fun x => H x i) : ∫ x, (fderiv ℝ H x).det = 0 := by
  set h : (Fin n → ℝ) → ℝ := fun x => H x i with hh
  have hhs : ContDiff ℝ ∞ h := (contDiff_apply ℝ ℝ i).comp hH
  have hJ : ∀ x j, jacobian H x i j = fderiv ℝ h x (Pi.single j 1) := fun x j =>
    jacobian_eq_fderiv_apply H x ((hH.differentiable (by simp)) x) i j
  have hexp : ∀ x, (fderiv ℝ H x).det =
      ∑ j, cofactorFn H i j x * fderiv ℝ h x (Pi.single j 1) := by
    intro x
    rw [det_fderiv_eq_det_jacobian]
    have := det_update_eq_sum (jacobian H x) i (jacobian H x i)
    rw [Function.update_eq_self] at this
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJ, mul_comm]; rfl
  have hcof := contDiff_cofactorFn H hH i
  have hcd : ∀ j, Continuous fun x => fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) := fun j =>
    ((hcof j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hhd : ∀ j, Continuous fun x => fderiv ℝ h x (Pi.single j 1) := fun j =>
    (hhs.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : ∀ j, Integrable (fun x => fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) * h x) :=
    fun j => ((hcd j).mul hhs.continuous).integrable_of_hasCompactSupport hi.mul_left
  have i2 : ∀ j, Integrable (fun x => cofactorFn H i j x * fderiv ℝ h x (Pi.single j 1)) :=
    fun j => ((hcof j).continuous.mul (hhd j)).integrable_of_hasCompactSupport
      (hi.fderiv_apply (𝕜 := ℝ) (Pi.single j 1)).mul_left
  have i3 : ∀ j, Integrable (fun x => cofactorFn H i j x * h x) :=
    fun j => ((hcof j).continuous.mul hhs.continuous).integrable_of_hasCompactSupport hi.mul_left
  have hibp : ∀ j, ∫ x, cofactorFn H i j x * fderiv ℝ h x (Pi.single j 1) =
      - ∫ x, fderiv ℝ (cofactorFn H i j) x (Pi.single j 1) * h x := fun j =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (i1 j) (i2 j) (i3 j)
      (fun x _ => ((hcof j).differentiable (by simp)) x)
      (fun x _ => (hhs.differentiable (by simp)) x)
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ => i2 j]
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun j _ => i1 j]
  simp_rw [← Finset.sum_mul, sum_fderiv_cofactorFn_eq_zero H hH i, zero_mul, integral_zero, neg_zero]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ChangeOfVariablesDegree
