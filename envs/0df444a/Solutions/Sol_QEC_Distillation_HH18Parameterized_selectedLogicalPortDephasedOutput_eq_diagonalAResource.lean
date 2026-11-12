-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.selectedLogicalPortDephasedOutput_eq_diagonalAResource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:03:50.60791+00:00
-- url     : https://prove2.me/submissions/a9351560-0172-48eb-b14e-f31ff0479f06

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPortSupport
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPort
import Theorems.Thm_QEC_Distillation_OneQubitABasisSupport_aBasisDephasing_mapDensity_eq_diagonalAResource_at_measuredRate


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
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    selectedLogicalPortDephasedOutput h hdegree epsilon port =
      diagonalAResource (selectedLogicalPortRawParameter h hdegree epsilon port) := by
  unfold selectedLogicalPortDephasedOutput
  apply OneQubitABasisSupport.aBasisDephasing_mapDensity_eq_diagonalAResource_at_measuredRate
  rfl
end QEC.Distillation.HH18Parameterized
