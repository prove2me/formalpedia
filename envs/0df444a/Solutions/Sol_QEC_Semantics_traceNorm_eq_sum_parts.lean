-- Prove2me | solution 1 for QEC.Semantics.traceNorm_eq_sum_parts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:18:16.974569+00:00
-- url     : https://prove2.me/submissions/e687a921-3f3a-4f62-a28c-5f0afbb27a77

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_traceNorm_nonneg
import Theorems.Thm_QEC_Semantics_traceNorm_add_le
import Theorems.Thm_QEC_Semantics_traceNorm_eq_re_trace_of_positive
import Theorems.Thm_QEC_Semantics_positivePart_sub_negativePart
import Theorems.Thm_QEC_Semantics_positivePart_positive
import Theorems.Thm_QEC_Semantics_negativePart_positive
import Theorems.Thm_QEC_Semantics_spectralSign_norm_le_one
import Theorems.Thm_QEC_Semantics_tracePairing_spectralSign
import Theorems.Thm_QEC_Semantics_traceNorm_neg
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Semantics.traceNorm_neg

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution [Nontrivial H]
    (A : Operator H) (hA : A.IsSymmetric) :
    traceNorm A = traceNorm (positivePart A) + traceNorm (negativePart A) := by
  apply le_antisymm
  · have hdecomp : positivePart A - negativePart A = A :=
      positivePart_sub_negativePart A hA
    calc
      traceNorm A = traceNorm (positivePart A - negativePart A) :=
        congrArg traceNorm hdecomp.symm
      _ ≤ traceNorm (positivePart A) + traceNorm (-negativePart A) := by
        simpa [sub_eq_add_neg] using traceNorm_add_le (positivePart A) (-negativePart A)
      _ = traceNorm (positivePart A) + traceNorm (negativePart A) := by
        rw [traceNorm_neg]
  · have hpair := (tracePairing A).le_opNorm (spectralSign A)
    have hpair_le : ‖tracePairing A (spectralSign A)‖ ≤ traceNorm A := by
      calc
        ‖tracePairing A (spectralSign A)‖ ≤
            traceNorm A * ‖spectralSign A‖ := hpair
        _ ≤ traceNorm A * 1 :=
          mul_le_mul_of_nonneg_left (spectralSign_norm_le_one A) (traceNorm_nonneg A)
        _ = traceNorm A := mul_one _
    rw [tracePairing_spectralSign A hA] at hpair_le
    have hpositive := positivePart_positive A
    have hnegative := negativePart_positive A
    have htrace_nonneg :
        0 ≤ LinearMap.trace Complex H (positivePart A) +
          LinearMap.trace Complex H (negativePart A) :=
      add_nonneg hpositive.trace_nonneg hnegative.trace_nonneg
    have hnorm_trace :
        ‖LinearMap.trace Complex H (positivePart A) +
          LinearMap.trace Complex H (negativePart A)‖ =
          Complex.re (LinearMap.trace Complex H (positivePart A) +
            LinearMap.trace Complex H (negativePart A)) := by
      have hcoe := Complex.eq_coe_norm_of_nonneg htrace_nonneg
      simpa using congrArg Complex.re hcoe.symm
    calc
      traceNorm (positivePart A) + traceNorm (negativePart A) =
          Complex.re (LinearMap.trace Complex H (positivePart A)) +
            Complex.re (LinearMap.trace Complex H (negativePart A)) := by
        rw [traceNorm_eq_re_trace_of_positive _ hpositive,
          traceNorm_eq_re_trace_of_positive _ hnegative]
      _ = Complex.re (LinearMap.trace Complex H (positivePart A) +
            LinearMap.trace Complex H (negativePart A)) := by
        rw [Complex.add_re]
      _ = ‖LinearMap.trace Complex H (positivePart A) +
            LinearMap.trace Complex H (negativePart A)‖ := hnorm_trace.symm
      _ ≤ traceNorm A := hpair_le
end QEC.Semantics
