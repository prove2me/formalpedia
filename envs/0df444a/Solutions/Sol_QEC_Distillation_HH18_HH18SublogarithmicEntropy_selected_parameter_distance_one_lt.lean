-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_parameter_distance_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:37:50.771213+00:00
-- url     : https://prove2.me/submissions/a79a75de-63d9-4363-8d1a-08ba4127b7da

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution (A D j : Nat)
    (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    1 < parameterDistance A D j := by
  have hscaled : 3 * A * j < D * j :=
    Nat.mul_lt_mul_of_pos_right hwindow hj
  have hindex : parameterW A j + 1 ≤ parameterR D j := by
    unfold parameterW parameterR
    have htwice : 2 * (3 * A * j) < 2 * (D * j) :=
      Nat.mul_lt_mul_of_pos_left hscaled (by omega)
    calc
      6 * A * j + 1 = 2 * (3 * A * j) + 1 := by ring
      _ ≤ 2 * (D * j) := Nat.succ_le_iff.mpr htwice
      _ = 2 * D * j := by ring
  have hrow : 1 < parameterR D j + 1 := by
    have hDj : 0 < D * j := Nat.mul_pos hD hj
    unfold parameterR
    have htwoDj : 0 < 2 * (D * j) := Nat.mul_pos (by omega) hDj
    calc
      1 ≤ 2 * (D * j) := htwoDj
      _ < 2 * (D * j) + 1 := Nat.lt_succ_self _
      _ = 2 * D * j + 1 := by ring
  calc
    1 < parameterR D j + 1 := hrow
    _ = Nat.choose (parameterR D j + 1) (parameterR D j) := by
      exact (Nat.choose_succ_self_right _).symm
    _ ≤ parameterDistance A D j := by
      unfold parameterDistance binomialTail
      apply Finset.single_le_sum (fun i _ => Nat.zero_le _)
      exact Finset.mem_Icc.mpr ⟨hindex, Nat.le_succ _⟩
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
