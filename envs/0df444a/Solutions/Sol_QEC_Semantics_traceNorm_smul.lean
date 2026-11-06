-- Prove2me | solution 1 for QEC.Semantics.traceNorm_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:40:15.913983+00:00
-- url     : https://prove2.me/submissions/ddd34d22-7735-4e5e-ac83-ffa451e4e185

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_tracePairing_smul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution (c : Complex) (A : Operator H) :
    traceNorm (c • A) = ‖c‖ * traceNorm A := by
  rw [traceNorm, traceNorm, tracePairing_smul]
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_smul_le c _
  · by_cases hc : c = 0
    · rw [hc]
      simp only [norm_zero, zero_mul]
      exact ContinuousLinearMap.opNorm_nonneg _
    · have h : ‖tracePairing A‖ ≤ ‖c⁻¹‖ * ‖c • tracePairing A‖ := by
        convert ContinuousLinearMap.opNorm_smul_le c⁻¹ (c • tracePairing A) using 1
        simp [hc]
      calc
        ‖c‖ * ‖tracePairing A‖ ≤ ‖c‖ * (‖c⁻¹‖ * ‖c • tracePairing A‖) :=
          mul_le_mul_of_nonneg_left h (norm_nonneg c)
        _ = ‖c • tracePairing A‖ := by
          rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc), one_mul]
end QEC.Semantics
