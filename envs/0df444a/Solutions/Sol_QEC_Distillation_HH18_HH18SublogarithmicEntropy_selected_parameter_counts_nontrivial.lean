-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_parameter_counts_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:35:13.216499+00:00
-- url     : https://prove2.me/submissions/2a86e63f-38ca-4a1d-9da9-804546e79d79

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selected_parameter_length_pos
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selected_parameter_dimension_pos
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selected_parameter_distance_one_lt

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution (A D j : Nat)
    (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    0 < parameterLength A D j ∧ 0 < parameterDimension A D j ∧
      1 < parameterDistance A D j :=
  ⟨selected_parameter_length_pos A D j hD hwindow hj,
    selected_parameter_dimension_pos A D j,
    selected_parameter_distance_one_lt A D j hD hwindow hj⟩
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
