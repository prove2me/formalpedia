-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18OneLevelProtocolFamily_targetError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:33:24.622526+00:00
-- url     : https://prove2.me/submissions/922981eb-b027-4bc9-9b74-ceea5f7db69f

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (hh18OneLevelProtocolFamily epsilon).targetError PUnit.unit =
      (2 * residualCubicCoefficient) * epsilon.1 ^ 3 :=
  rfl
end QEC.Distillation.HH18Protocol
