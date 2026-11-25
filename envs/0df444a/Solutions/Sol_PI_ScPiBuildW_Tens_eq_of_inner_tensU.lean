-- Prove2me | solution 1 for PI.ScPiBuildW.Tens.eq_of_inner_tensU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:40.674707+00:00
-- url     : https://prove2.me/submissions/37215d16-77b8-438c-b0be-1bbdf93b78d8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
import Theorems.Thm_PI_ScPiBuildW_Tens_span_tensU

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
theorem _root_.solution {v v' : TV Vl} (h : ∀ x, ⟪tensU x, v⟫_ℂ = ⟪tensU x, v'⟫_ℂ) : v = v' := by
  have hd : ∀ x, ⟪v - v', tensU x⟫_ℂ = 0 := fun x => by
    rw [← inner_conj_symm, inner_sub_right, h x, sub_self, map_zero]
  have h0 : (innerSL ℂ (v - v')).toLinearMap = 0 :=
    LinearMap.ext_on_range span_tensU (fun x => by simpa using hd x)
  have h2 : ⟪v - v', v - v'⟫_ℂ = 0 := by
    have := LinearMap.congr_fun h0 (v - v')
    simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, LinearMap.zero_apply] at this
    exact this
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h2)
end PI.ScPiBuildW.Tens
