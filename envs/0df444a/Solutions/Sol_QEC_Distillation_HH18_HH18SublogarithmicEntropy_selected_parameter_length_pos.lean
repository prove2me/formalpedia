-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_parameter_length_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:31:42.328752+00:00
-- url     : https://prove2.me/submissions/6f48bafe-0524-46a5-ae11-516fa9857b01

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
import Theorems.Thm_QEC_Distillation_HH18_HH18BinomialTailAsymptotics_choose_succ_le_tail


set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution (A D j : Nat)
    (_hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    0 < parameterLength A D j := by
  have hindex : parameterW A j < parameterM D j := by
    unfold parameterW parameterM
    have hscaled : 3 * A * j < D * j :=
      Nat.mul_lt_mul_of_pos_right hwindow hj
    have htwice : 2 * (3 * A * j) < 2 * (D * j) :=
      Nat.mul_lt_mul_of_pos_left hscaled (by omega)
    calc
      6 * A * j = 2 * (3 * A * j) := by ring
      _ < 2 * (D * j) := htwice
      _ ≤ 6 * (D * j) := Nat.mul_le_mul_right (D * j) (by omega)
      _ = 6 * D * j := by ring
      _ < 6 * D * j + 1 := Nat.lt_succ_self _
  unfold parameterLength
  exact lt_of_lt_of_le
    (Nat.choose_pos (Nat.succ_le_iff.mpr hindex))
    (HH18BinomialTailAsymptotics.choose_succ_le_tail _ _
      (Nat.succ_le_iff.mpr hindex))
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
