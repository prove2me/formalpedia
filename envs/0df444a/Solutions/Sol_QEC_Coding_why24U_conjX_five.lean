-- Prove2me | solution 1 for QEC.Coding.why24U_conjX_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:23:28.399496+00:00
-- url     : https://prove2.me/submissions/36b76d71-82ff-406f-b90e-e25242624ca3

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Coding_why24U_adjoint
import Theorems.Thm_QEC_Coding_why24FrobeniusRootFour_pow_four
import Theorems.Thm_QEC_Coding_why24_trace_sq
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.why24QuditZ_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Coding.why24U_apply
section
noncomputable section
namespace QEC.Coding
open scoped BigOperators
private theorem why24_trace_eq_of_pow_four {x y : F1024} (hxy : x ^ 4 = y) :
    Algebra.trace (ZMod 2) F1024 x = Algebra.trace (ZMod 2) F1024 y := by
  calc
    Algebra.trace (ZMod 2) F1024 x = Algebra.trace (ZMod 2) F1024 (x ^ 2) :=
      (why24_trace_sq x).symm
    _ = Algebra.trace (ZMod 2) F1024 ((x ^ 2) ^ 2) :=
      (why24_trace_sq (x ^ 2)).symm
    _ = Algebra.trace (ZMod 2) F1024 (x ^ 4) := by ring_nf
    _ = Algebra.trace (ZMod 2) F1024 y := by rw [hxy]
private theorem why24_trace_u_five_conjugation (β γ η : F1024) :
    Algebra.trace (ZMod 2) F1024 (β * η ^ 5) +
      Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 5) =
        Algebra.trace (ZMod 2) F1024 (β * γ ^ 5) +
          Algebra.trace (ZMod 2) F1024
            ((why24FrobeniusRootFour (β * γ) + β * γ ^ 4) * η) := by
  have hpowfour : (why24FrobeniusRootFour (β * γ) * η) ^ 4 = β * γ * η ^ 4 := by
    calc
      (why24FrobeniusRootFour (β * γ) * η) ^ 4 =
          why24FrobeniusRootFour (β * γ) ^ 4 * η ^ 4 := by rw [mul_pow]
      _ = β * γ * η ^ 4 := by rw [why24FrobeniusRootFour_pow_four]
  have hroot :
      Algebra.trace (ZMod 2) F1024 (why24FrobeniusRootFour (β * γ) * η) =
        Algebra.trace (ZMod 2) F1024 (β * γ * η ^ 4) :=
    why24_trace_eq_of_pow_four hpowfour
  have htwo : (2 : F1024) = 0 := CharP.ofNat_eq_zero' (R := F1024) 2 2 (by norm_num)
  have hfive : (5 : F1024) = 1 := by
    calc
      (5 : F1024) = 2 * 2 + 1 := by norm_num
      _ = 1 := by rw [htwo]; ring
  have hten : (10 : F1024) = 0 := by
    calc
      (10 : F1024) = 5 * 2 := by norm_num
      _ = 0 := by rw [htwo, mul_zero]
  have hbinomial : β * (η + γ) ^ 5 =
      β * η ^ 5 + β * γ ^ 5 + β * γ * η ^ 4 + β * γ ^ 4 * η := by
    ring_nf
    rw [hfive, hten]
    ring
  rw [hbinomial, map_add, map_add, map_add]
  rw [show (why24FrobeniusRootFour (β * γ) + β * γ ^ 4) * η =
      why24FrobeniusRootFour (β * γ) * η + β * γ ^ 4 * η by ring, map_add]
  rw [hroot]
  let a : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * η ^ 5)
  let b : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 5)
  let c : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ * η ^ 4)
  let d : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 4 * η)
  change a + (a + b + c + d) = b + (c + d)
  calc
    a + (a + b + c + d) = (a + a) + b + c + d := by ac_rfl
    _ = 0 + b + c + d := by rw [CharTwo.add_self_eq_zero]
    _ = b + (c + d) := by ac_rfl
end QEC.Coding
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (β γ : F1024) :
    why24U β 5 * why24QuditX γ * LinearMap.adjoint (why24U β 5) =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * γ ^ 5)) •
        (why24QuditX γ *
          why24QuditZ (why24FrobeniusRootFour (β * γ) + β * γ ^ 4)) := by
  rw [why24U_adjoint]
  ext ψ η
  simp only [Module.End.mul_apply, why24U_apply, why24QuditX_apply]
  change PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * η ^ 5)) *
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 5)) * ψ (η + γ)) =
    PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * γ ^ 5)) *
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024
          ((why24FrobeniusRootFour (β * γ) + β * γ ^ 4) * (η + γ))) *
        ψ (η + γ))
  rw [← mul_assoc]
  conv_rhs => rw [← mul_assoc]
  rw [← PauliSymplectic.binaryPhaseScalar_add]
  conv_rhs => rw [← PauliSymplectic.binaryPhaseScalar_add]
  have hshift : η + γ + γ = η := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have htrace := why24_trace_u_five_conjugation β γ (η + γ)
  rw [hshift] at htrace
  have htrace' :
      Algebra.trace (ZMod 2) F1024 (β * η ^ 5) +
        Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 5) =
          Algebra.trace (ZMod 2) F1024 (β * γ ^ 5) +
            Algebra.trace (ZMod 2) F1024
              ((why24FrobeniusRootFour (β * γ) + β * γ ^ 4) * (η + γ)) := by
    rw [add_comm]
    exact htrace
  rw [htrace']
end QEC.Coding
