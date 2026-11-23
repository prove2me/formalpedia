-- Prove2me | solution 1 for PI.ScPiBuildW.Tens.inner_tensU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:11.287285+00:00
-- url     : https://prove2.me/submissions/7319df66-150d-4417-8e36-ef6ac735eca6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
import Theorems.Thm_PI_ScPiBuildW_Tens_tensU_apply
import Theorems.Thm_PI_ScPiBuildW_Tens_prod_sum_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open Module
open PI PI.ScPiBuildW PI.ScPiBuildW.Tens
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Vl : ι → Type} [∀ i, NormedAddCommGroup (Vl i)] [∀ i, InnerProductSpace ℂ (Vl i)]
  [∀ i, FiniteDimensional ℂ (Vl i)]
namespace PI.ScPiBuildW.Tens
theorem _root_.solution (x y : ∀ i, Vl i) : ⟪tensU x, tensU y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ := by
  rw [PiLp.inner_apply]
  simp only [tensU_apply, RCLike.inner_apply, map_prod]
  have h : ∀ i, ⟪x i, y i⟫_ℂ = ∑ j, (starRingEnd ℂ) ⟪bas Vl i j, x i⟫_ℂ * ⟪bas Vl i j, y i⟫_ℂ := by
    intro i
    rw [← (bas Vl i).sum_inner_mul_inner (x i) (y i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_conj_symm]
  simp_rw [h, prod_sum_pi, ← Finset.prod_mul_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  ring
end PI.ScPiBuildW.Tens
