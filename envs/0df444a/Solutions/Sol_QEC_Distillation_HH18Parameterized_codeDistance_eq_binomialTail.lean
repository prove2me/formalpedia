-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.codeDistance_eq_binomialTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:54:47.340643+00:00
-- url     : https://prove2.me/submissions/bacbbafb-48bd-4541-ae6e-d820b674997a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution (r w : Nat) :
    codeDistance r w = binomialTail (r + 1) w :=
  rfl
end QEC.Distillation.HH18Parameterized
