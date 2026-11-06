-- Prove2me | solution 1 for QEC.Semantics.traceNorm_eq_re_trace_of_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:43:32.130941+00:00
-- url     : https://prove2.me/submissions/902a7c65-4c14-4640-8458-07bc544c0e67

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_traceNorm_sum_le
import Theorems.Thm_QEC_Semantics_traceNorm_rankOne_self_le
import Theorems.Thm_QEC_Semantics_norm_trace_le_traceNorm
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
theorem _root_.solution [Nontrivial H]
    (A : Operator H) (hA : LinearMap.IsPositive A) :
    traceNorm A = Complex.re (LinearMap.trace Complex H A) := by
  have hAclm : (LinearMap.toContinuousLinearMap A).IsPositive :=
    (LinearMap.isPositive_toContinuousLinearMap_iff A).mpr hA
  obtain ⟨m, u, hu⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hAclm
  have hA_sum : A = ∑ i : Fin m,
      (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap := by
    simpa using congrArg ContinuousLinearMap.toLinearMap hu
  have htrace : Complex.re (LinearMap.trace Complex H A) =
      ∑ i : Fin m, ‖u i‖ ^ 2 := by
    rw [hA_sum, map_sum]
    simp only [InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    norm_num [pow_two, Complex.mul_re]
  apply le_antisymm
  · calc
      traceNorm A = traceNorm (∑ i : Fin m,
          (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap) :=
        congrArg traceNorm hA_sum
      _ ≤ ∑ i : Fin m,
          traceNorm (InnerProductSpace.rankOne Complex (u i) (u i)).toLinearMap := by
        exact traceNorm_sum_le Finset.univ _
      _ ≤ ∑ i : Fin m, ‖u i‖ ^ 2 := by
        exact Finset.sum_le_sum fun i _ => traceNorm_rankOne_self_le (u i)
      _ = Complex.re (LinearMap.trace Complex H A) := htrace.symm
  · exact (Complex.re_le_norm _).trans (norm_trace_le_traceNorm A)
end QEC.Semantics
