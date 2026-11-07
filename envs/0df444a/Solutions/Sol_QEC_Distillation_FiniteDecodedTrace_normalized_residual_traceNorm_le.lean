-- Prove2me | solution 1 for QEC.Distillation.FiniteDecodedTrace.normalized_residual_traceNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:15:48.596679+00:00
-- url     : https://prove2.me/submissions/6abfafcb-b1ed-4826-8e18-090ddc721297

import Definitions.Def_QEC_Distillation_Core_FiniteCentering
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Theorems.Thm_QEC_Semantics_traceNorm_smul


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.FiniteDecodedTrace
open Semantics
open scoped BigOperators
universe u v
namespace QEC.Distillation.FiniteDecodedTrace
theorem _root_.solution
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (success residualMass : ℝ) (residual : Operator H)
    (hsuccess : 0 < success)
    (hresidual : traceNorm residual ≤ 2 * residualMass) :
    traceNorm ((success : Complex)⁻¹ • residual) ≤ 2 * (residualMass / success) := by
  rw [traceNorm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsuccess]
  calc
    success⁻¹ * traceNorm residual ≤ success⁻¹ * (2 * residualMass) :=
      mul_le_mul_of_nonneg_left hresidual (by positivity)
    _ = 2 * (residualMass / success) := by
      field_simp [ne_of_gt hsuccess]
end QEC.Distillation.FiniteDecodedTrace
