-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.noisyResources_permitted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:13:29.208281+00:00
-- url     : https://prove2.me/submissions/26abe8f4-3ed3-4c12-bd55-688020dccf6e

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalTypes
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Postselection
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourcePreparation

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instClassicalDecidable
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    InputErrorModel.Permits (.independent (independentInputModel epsilon))
      (noisyResources epsilon) := by
  constructor
  · intro slot
    rfl
  · rfl
end QEC.Distillation.HH18Protocol
