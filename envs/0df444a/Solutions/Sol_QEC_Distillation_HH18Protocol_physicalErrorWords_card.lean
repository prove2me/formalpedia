-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.physicalErrorWords_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:14:14.457138+00:00
-- url     : https://prove2.me/submissions/13d2da5c-85ae-4dcc-983d-d44e0bc230ab

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
theorem _root_.solution :
    physicalErrorWords.card = Fintype.card PhysicalErrorWord := by
  rfl
end QEC.Distillation.HH18Protocol
