-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.hasDerivAt_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:52.470352+00:00
-- url     : https://prove2.me/submissions/a09705d6-cc11-4e2d-bf30-088ec08ef48a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_adj_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_det_updateCol_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
open MeasureTheory Filter Topology Set
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (A + (s : ℂ) • B).det)
      (∑ k, ∑ j, (A + (t : ℂ) • B).adjugate k j * B j k) t := by
  have hent : ∀ i j, HasDerivAt (fun s : ℝ => (A + (s : ℂ) • B) i j) (B i j) t := by
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const (B i j)).const_add (A i j)
  have hdet : HasDerivAt (fun s : ℝ => (A + (s : ℂ) • B).det)
      (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ k, (∏ l ∈ Finset.univ.erase k, (A + (t : ℂ) • B) (σ l) l) • B (σ k) k) t := by
    simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
    have hs := HasDerivAt.sum (u := Finset.univ)
      (A := fun σ (s : ℝ) => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, (A + (s : ℂ) • B) (σ i) i)
      (A' := fun σ => ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ k, (∏ l ∈ Finset.univ.erase k, (A + (t : ℂ) • B) (σ l) l) • B (σ k) k)
      (fun σ _ => by
        have h := (HasDerivAt.finset_prod (u := Finset.univ) fun k _ => hent (σ k) k).const_mul
          (((Equiv.Perm.sign σ : ℤ) : ℂ))
        simp only [Finset.prod_apply] at h
        exact h)
    rw [Finset.sum_fn] at hs
    exact hs
  convert hdet using 1
  simp_rw [adj_sum, det_updateCol_eq, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring
end ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
