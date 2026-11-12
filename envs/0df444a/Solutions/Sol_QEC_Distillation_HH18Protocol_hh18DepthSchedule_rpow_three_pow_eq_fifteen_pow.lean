-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthSchedule_rpow_three_pow_eq_fifteen_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:33:01.511168+00:00
-- url     : https://prove2.me/submissions/823baea3-04df-46cb-b2de-2844964c6df0

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution (depth : Nat) :
    Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma =
      (15 : ℝ) ^ depth := by
  calc
    Real.rpow ((3 : ℝ) ^ depth) hh18DepthScheduleGamma =
        Real.exp (Real.log ((3 : ℝ) ^ depth) * hh18DepthScheduleGamma) := by
      exact Real.rpow_def_of_pos (by positivity) _
    _ = Real.exp ((depth : ℝ) * Real.log 15) := by
      unfold hh18DepthScheduleGamma
      congr 1
      rw [Real.log_pow]
      field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))]
    _ = Real.rpow 15 (depth : ℝ) := by
      symm
      calc
        Real.rpow 15 (depth : ℝ) = Real.exp (Real.log 15 * (depth : ℝ)) :=
          Real.rpow_def_of_pos (by norm_num) _
        _ = Real.exp ((depth : ℝ) * Real.log 15) :=
          congrArg Real.exp (mul_comm _ _)
    _ = (15 : ℝ) ^ depth := Real.rpow_natCast _ _
end QEC.Distillation.HH18Protocol
