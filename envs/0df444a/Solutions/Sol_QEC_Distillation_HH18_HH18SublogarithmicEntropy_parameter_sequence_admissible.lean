-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.parameter_sequence_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:43:14.764432+00:00
-- url     : https://prove2.me/submissions/aef6985f-3d44-4514-b2a9-7c898f8e4c49

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution
    (A D j : Nat) (hA : 0 < A) (hD : 0 < D)
    (hwindow : 3 * A < D) (hj : 0 < j) :
    parameterM D j = 3 * parameterR D j + 1 ∧
      (parameterW A j : ℚ) =
        3 * (parameterR D j : ℚ) * ((A : ℚ) / D) ∧
      Admissible (parameterW A j) (parameterR D j) (parameterM D j) := by
  constructor
  · unfold parameterM parameterR
    ring
  constructor
  · unfold parameterW parameterR
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
    push_cast
    field_simp [hD0]
    ring
  · unfold parameterW parameterR parameterM Admissible
    have hstrict : 12 * A * j < 4 * D * j := by
      have hscaled : (3 * A) * j < D * j :=
        Nat.mul_lt_mul_of_pos_right hwindow hj
      calc
        12 * A * j = 4 * ((3 * A) * j) := by ring
        _ < 4 * (D * j) := Nat.mul_lt_mul_of_pos_left hscaled (by omega)
        _ = 4 * D * j := by ring
    constructor
    · omega
    constructor
    · convert hstrict using 1 <;> ring
    · calc
        2 * (2 * D * j) = 4 * D * j := by ring
        _ ≤ 6 * D * j := Nat.mul_le_mul_right j (by omega)
        _ < 6 * D * j + 1 := Nat.lt_succ_self _
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
