-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.selectedCSSCode_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:12:39.757076+00:00
-- url     : https://prove2.me/submissions/71b0fb46-ec6e-4420-a6be-44ae416726f5

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_SelectedCode
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_cssParameters


set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding
open Coding.PuncturedReedMuller
open QEC.Distillation.HH18PuncturedReedMuller
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution (A D j : Nat)
    (hA : 0 < A) (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    Length (ZMod 2) (PhysicalSite (parameterM D j) (parameterW A j)) =
        parameterLength A D j ∧
      Length (ZMod 2) (PhysicalSite (parameterM D j) (parameterW A j)) -
          Dimension (xCode (parameterW A j) (parameterR D j) (parameterM D j)) -
          Dimension (zCode (parameterW A j) (parameterR D j) (parameterM D j)) =
        parameterDimension A D j ∧
      Module.finrank Complex
          (selectedCSSCode A D j hA hD hwindow hj).stabilizer.code.carrier =
        2 ^ parameterDimension A D j ∧
      StabilizerCode.SemanticStabilizerDistance
          (sourceValidStabilizer
            (selected_parameter_admissible A D j hA hD hwindow hj))
          (parameterDistance A D j) := by
  exact cssParameters (selected_parameter_admissible A D j hA hD hwindow hj)
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
