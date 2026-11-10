-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryCSSCode_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:46:48.640168+00:00
-- url     : https://prove2.me/submissions/b71d9014-db3a-404f-a782-8a8cdc4a22eb

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinarySelfDual
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCubicBridge
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTensorEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryFamily
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryDistance_detects
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryDistance_fails_succ
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_code_eq_cssCode


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat) :
    QuditSubsystem.BPTMeasurementDistance (binaryCSSCode i).stabilizer.code (binaryDistance i) ∧
      ¬ QuditSubsystem.BPTMeasurementDistance (binaryCSSCode i).stabilizer.code (binaryDistance i + 1) := by
  rw [← binaryEncodedCode_code_eq_cssCode]
  exact ⟨binaryDistance_detects i, binaryDistance_fails_succ i⟩
end QEC.Distillation.Ngu24Binary
