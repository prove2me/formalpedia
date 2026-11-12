-- Prove2me | solution 2 for QEC.Distillation.HH18Parameterized.noisyResources_permitted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:38:04.307611+00:00
-- url     : https://prove2.me/submissions/a016877f-dc7c-40f9-a21e-c5d4dd9b9339

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution (m w : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    InputErrorModel.Permits (.independent (independentInputModel m w epsilon))
      (noisyResources m w epsilon) := by
  constructor
  · intro slot
    rfl
  · rfl
end QEC.Distillation.HH18Parameterized
