-- Prove2me | solution 1 for QEC.Coding.why24UOneSeven_conjX_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:27:07.894749+00:00
-- url     : https://prove2.me/submissions/a525f19c-c393-4590-9b49-4e70325993e0

import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Coding_why24U_adjoint
import Theorems.Thm_QEC_Coding_why24FrobeniusRootTwo_sq
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
private theorem why24_trace_eq_of_sq {x y : F1024} (hxy : x ^ 2 = y) :
    Algebra.trace (ZMod 2) F1024 x = Algebra.trace (ZMod 2) F1024 y := by
  rw [← why24_trace_sq x, hxy]
private theorem why24_trace_eq_of_pow_four {x y : F1024} (hxy : x ^ 4 = y) :
    Algebra.trace (ZMod 2) F1024 x = Algebra.trace (ZMod 2) F1024 y := by
  calc
    Algebra.trace (ZMod 2) F1024 x = Algebra.trace (ZMod 2) F1024 (x ^ 2) :=
      (why24_trace_sq x).symm
    _ = Algebra.trace (ZMod 2) F1024 ((x ^ 2) ^ 2) :=
      (why24_trace_sq (x ^ 2)).symm
    _ = Algebra.trace (ZMod 2) F1024 (x ^ 4) := by ring_nf
    _ = Algebra.trace (ZMod 2) F1024 y := by rw [hxy]
private theorem why24_trace_u_seven_conjugation (β γ η : F1024) :
    Algebra.trace (ZMod 2) F1024 (β * η ^ 7) +
      Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 7) =
        Algebra.trace (ZMod 2) F1024 (β * γ ^ 7) +
          Algebra.trace (ZMod 2) F1024
            ((why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) * η ^ 3) +
          Algebra.trace (ZMod 2) F1024 ((β * γ ^ 2) * η ^ 5) +
          Algebra.trace (ZMod 2) F1024
            ((why24FrobeniusRootFour (β * γ ^ 3) +
                why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6) * η) := by
  have hsix : (why24FrobeniusRootTwo (β * γ) * η ^ 3) ^ 2 = β * γ * η ^ 6 := by
    calc
      (why24FrobeniusRootTwo (β * γ) * η ^ 3) ^ 2 =
          why24FrobeniusRootTwo (β * γ) ^ 2 * (η ^ 3) ^ 2 := by rw [mul_pow]
      _ = β * γ * η ^ 6 := by rw [why24FrobeniusRootTwo_sq]; ring
  have hfour : (why24FrobeniusRootFour (β * γ ^ 3) * η) ^ 4 =
      β * γ ^ 3 * η ^ 4 := by
    calc
      (why24FrobeniusRootFour (β * γ ^ 3) * η) ^ 4 =
          why24FrobeniusRootFour (β * γ ^ 3) ^ 4 * η ^ 4 := by rw [mul_pow]
      _ = β * γ ^ 3 * η ^ 4 := by rw [why24FrobeniusRootFour_pow_four]
  have htwo : (why24FrobeniusRootTwo (β * γ ^ 5) * η) ^ 2 =
      β * γ ^ 5 * η ^ 2 := by
    calc
      (why24FrobeniusRootTwo (β * γ ^ 5) * η) ^ 2 =
          why24FrobeniusRootTwo (β * γ ^ 5) ^ 2 * η ^ 2 := by rw [mul_pow]
      _ = β * γ ^ 5 * η ^ 2 := by rw [why24FrobeniusRootTwo_sq]
  have hrootSix :
      Algebra.trace (ZMod 2) F1024 (why24FrobeniusRootTwo (β * γ) * η ^ 3) =
        Algebra.trace (ZMod 2) F1024 (β * γ * η ^ 6) :=
    why24_trace_eq_of_sq hsix
  have hrootFour :
      Algebra.trace (ZMod 2) F1024 (why24FrobeniusRootFour (β * γ ^ 3) * η) =
        Algebra.trace (ZMod 2) F1024 (β * γ ^ 3 * η ^ 4) :=
    why24_trace_eq_of_pow_four hfour
  have hrootTwo :
      Algebra.trace (ZMod 2) F1024 (why24FrobeniusRootTwo (β * γ ^ 5) * η) =
        Algebra.trace (ZMod 2) F1024 (β * γ ^ 5 * η ^ 2) :=
    why24_trace_eq_of_sq htwo
  have htwoChar : (2 : F1024) = 0 :=
    CharP.ofNat_eq_zero' (R := F1024) 2 2 (by norm_num)
  have hthree : (3 : F1024) = 1 := by
    calc
      (3 : F1024) = 2 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have hfive : (5 : F1024) = 1 := by
    calc
      (5 : F1024) = 2 * 2 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have hseven : (7 : F1024) = 1 := by
    calc
      (7 : F1024) = 2 * 3 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have htwentyOne : (21 : F1024) = 1 := by
    calc
      (21 : F1024) = 2 * 10 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have hthirtyFive : (35 : F1024) = 1 := by
    calc
      (35 : F1024) = 2 * 17 + 1 := by norm_num
      _ = 1 := by rw [htwoChar]; ring
  have hbinomial : β * (η + γ) ^ 7 =
      β * η ^ 7 + β * γ ^ 7 + β * γ * η ^ 6 + β * γ ^ 2 * η ^ 5 +
        β * γ ^ 3 * η ^ 4 + β * γ ^ 4 * η ^ 3 + β * γ ^ 5 * η ^ 2 +
          β * γ ^ 6 * η := by
    ring_nf
    rw [hseven, htwentyOne, hthirtyFive]
    ring
  rw [hbinomial]
  repeat' rw [map_add]
  rw [show (why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) * η ^ 3 =
      why24FrobeniusRootTwo (β * γ) * η ^ 3 + β * γ ^ 4 * η ^ 3 by ring,
    show (why24FrobeniusRootFour (β * γ ^ 3) +
        why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6) * η =
      why24FrobeniusRootFour (β * γ ^ 3) * η +
        why24FrobeniusRootTwo (β * γ ^ 5) * η + β * γ ^ 6 * η by ring]
  repeat' rw [map_add]
  rw [hrootSix, hrootFour, hrootTwo]
  let a : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * η ^ 7)
  let b : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 7)
  let c : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ * η ^ 6)
  let d : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 2 * η ^ 5)
  let e : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 3 * η ^ 4)
  let f : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 4 * η ^ 3)
  let g : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 5 * η ^ 2)
  let h : ZMod 2 := Algebra.trace (ZMod 2) F1024 (β * γ ^ 6 * η)
  change a + (a + b + c + d + e + f + g + h) = b + (c + f) + d + (e + g + h)
  calc
    a + (a + b + c + d + e + f + g + h) =
        (a + a) + b + c + d + e + f + g + h := by ac_rfl
    _ = b + (c + f) + d + (e + g + h) := by
      rw [CharTwo.add_self_eq_zero]
      ac_rfl
private theorem why24U_conjX_seven (β γ : F1024) :
    why24U β 7 * why24QuditX γ * LinearMap.adjoint (why24U β 7) =
      PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * γ ^ 7)) •
        (why24QuditX γ *
          why24U (why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) 3 *
          why24U (β * γ ^ 2) 5 *
          why24QuditZ
            (why24FrobeniusRootFour (β * γ ^ 3) +
              why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6)) := by
  rw [why24U_adjoint]
  ext ψ η
  simp only [Module.End.mul_apply, why24U_apply, why24QuditX_apply, why24QuditZ_apply,
    smul_eq_mul]
  change PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * η ^ 7)) *
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 7)) * ψ (η + γ)) =
    PauliSymplectic.binaryPhaseScalar
      (Algebra.trace (ZMod 2) F1024 (β * γ ^ 7)) *
      (PauliSymplectic.binaryPhaseScalar
        (Algebra.trace (ZMod 2) F1024
          ((why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) * (η + γ) ^ 3)) *
        (PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 ((β * γ ^ 2) * (η + γ) ^ 5)) *
          (PauliSymplectic.binaryPhaseScalar
            (Algebra.trace (ZMod 2) F1024
              ((why24FrobeniusRootFour (β * γ ^ 3) +
                why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6) * (η + γ))) *
            ψ (η + γ))))
  rw [← mul_assoc]
  conv_rhs => rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  repeat' rw [← PauliSymplectic.binaryPhaseScalar_add]
  have hshift : η + γ + γ = η := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have htrace := why24_trace_u_seven_conjugation β γ (η + γ)
  rw [hshift] at htrace
  have htrace' :
      Algebra.trace (ZMod 2) F1024 (β * η ^ 7) +
        Algebra.trace (ZMod 2) F1024 (β * (η + γ) ^ 7) =
          Algebra.trace (ZMod 2) F1024 (β * γ ^ 7) +
            Algebra.trace (ZMod 2) F1024
              ((why24FrobeniusRootTwo (β * γ) + β * γ ^ 4) * (η + γ) ^ 3) +
            Algebra.trace (ZMod 2) F1024 ((β * γ ^ 2) * (η + γ) ^ 5) +
            Algebra.trace (ZMod 2) F1024
              ((why24FrobeniusRootFour (β * γ ^ 3) +
                  why24FrobeniusRootTwo (β * γ ^ 5) + β * γ ^ 6) * (η + γ)) := by
    rw [add_comm]
    exact htrace
  rw [htrace']
private theorem why24U_zero (n : ℕ) :
    why24U (0 : F1024) n = 1 := by
  ext ψ η
  simp [why24U_apply]
end QEC.Coding
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution :
    why24UOneSeven * why24QuditX (1 : F1024) * LinearMap.adjoint why24UOneSeven =
      PauliSymplectic.binaryPhaseScalar
          (Algebra.trace (ZMod 2) F1024 ((1 : F1024) ^ 7)) •
        (why24QuditX (1 : F1024) * why24U (1 : F1024) 5 * why24QuditZ (1 : F1024)) := by
  simpa [why24UOneSeven, why24FrobeniusRootTwo, why24FrobeniusRootFour,
    why24U_zero, CharTwo.add_self_eq_zero, mul_assoc] using
    why24U_conjX_seven (1 : F1024) (1 : F1024)
end QEC.Coding
