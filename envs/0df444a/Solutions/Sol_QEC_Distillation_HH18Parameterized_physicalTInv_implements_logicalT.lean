-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.physicalTInv_implements_logicalT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:54:53.941625+00:00
-- url     : https://prove2.me/submissions/dfd260cf-eca8-4aaf-8b6c-6432ab77776d

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_physicalTInv_implements_logicalT


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
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    (HH18PuncturedReedMuller.encodedCode h).ImplementsLogicalGate
      (HH18PuncturedReedMuller.physicalTInv w m)
      (HH18PuncturedReedMuller.logicalT w m) :=
  HH18PuncturedReedMuller.physicalTInv_implements_logicalT h hdegree
end QEC.Distillation.HH18Parameterized
