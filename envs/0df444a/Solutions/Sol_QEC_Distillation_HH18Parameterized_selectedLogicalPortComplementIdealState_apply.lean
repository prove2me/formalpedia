-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.selectedLogicalPortComplementIdealState_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:46:22.353078+00:00
-- url     : https://prove2.me/submissions/b14f1332-e468-4819-9122-5cb5cc91b304

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPortSupport
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSelectedPortClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instSelectedPortClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution (m w : Nat)
    (port : LogicalSite m w)
    (bits : Qubit.Bitstring (selectedLogicalPortSubsystem m w port).ComplementCoordinates) :
    selectedLogicalPortComplementIdealState m w port bits =
      (Real.sqrt 2 : Complex) *
        Triorthogonal.BinaryRowFamily.logicalMagicState (LogicalSite m w)
          (selectedLogicalPortAnchorBitstring m w port bits) :=
  rfl
end QEC.Distillation.HH18Parameterized
