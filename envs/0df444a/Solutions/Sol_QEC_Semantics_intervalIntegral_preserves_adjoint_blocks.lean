-- Prove2me | solution 1 for QEC.Semantics.intervalIntegral_preserves_adjoint_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:01:55.723313+00:00
-- url     : https://prove2.me/submissions/c97b692a-d837-4642-8238-01f097a49a34

import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_LieTrotter
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Theorems.Thm_QEC_Semantics_intervalIntegral_comp_comm
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg



set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
attribute [local instance] QEC.Semantics.finiteQuantumSystemComplete
set_option maxHeartbeats 800000
namespace QEC.Semantics
theorem _root_.solution
    (f : Real → ContinuousSuperoperator H) (a b : Real)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hab : a ≤ b) (A B : Operator H)
    (hsym : ∀ s ∈ Set.Icc a b, asOperatorSuperoperator (f s) B =
      LinearMap.adjoint (asOperatorSuperoperator (f s) A)) :
    asOperatorSuperoperator (∫ s in a..b, f s) B =
      LinearMap.adjoint (asOperatorSuperoperator (∫ s in a..b, f s) A) := by
  let Ac := LinearMap.toContinuousLinearMap A
  let Bc := LinearMap.toContinuousLinearMap B
  let evalA :=
    (ContinuousLinearMap.apply Complex (ContinuousOperator H) Ac).restrictScalars Real
  let evalB :=
    (ContinuousLinearMap.apply Complex (ContinuousOperator H) Bc).restrictScalars Real
  have hfA : IntervalIntegrable (fun s => f s Ac) MeasureTheory.volume a b :=
    ⟨evalA.integrable_comp hf.1, evalA.integrable_comp hf.2⟩
  have hs (s : Real) (hsab : s ∈ Set.Icc a b) :
      f s Bc = ContinuousLinearMap.adjoint (f s Ac) := by
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg (fun T : Operator H => T x) (hsym s hsab)
    rw [LinearMap.adjoint_eq_toCLM_adjoint] at h
    exact h
  have hcontinuous :
      (∫ s in a..b, f s Bc) =
        ContinuousLinearMap.adjoint (∫ s in a..b, f s Ac) := by
    calc
      (∫ s in a..b, f s Bc) =
          (∫ s in a..b, ContinuousLinearMap.adjoint (f s Ac)) := by
            apply intervalIntegral.integral_congr
            intro s hsab
            exact hs s (by simpa [Set.uIcc_of_le hab] using hsab)
      _ = ContinuousLinearMap.adjoint (∫ s in a..b, f s Ac) := by
            exact intervalIntegral_comp_comm continuousOperatorAdjointReal
              (fun s => f s Ac) a b hfA
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  apply congrArg ContinuousLinearMap.toLinearMap
  change (∫ s in a..b, f s) Bc =
    ContinuousLinearMap.adjoint ((∫ s in a..b, f s) Ac)
  change evalB (∫ s in a..b, f s) =
    ContinuousLinearMap.adjoint (evalA (∫ s in a..b, f s))
  rw [← intervalIntegral_comp_comm evalB f a b hf,
    ← intervalIntegral_comp_comm evalA f a b hf]
  exact hcontinuous
end QEC.Semantics
