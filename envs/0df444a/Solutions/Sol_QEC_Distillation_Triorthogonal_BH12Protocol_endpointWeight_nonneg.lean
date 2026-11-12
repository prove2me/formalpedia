-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.endpointWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:26:01.224261+00:00
-- url     : https://prove2.me/submissions/d6fd31ec-2dda-44f6-a20c-267b7b6c5e06

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.Triorthogonal.BH12Protocol
theorem _root_.solution (q : Nat) (p : ErrorParameter)
    (outcome : DistillationOutcome) : 0 ≤ endpointWeight q p outcome :=
  (protocolSyndromeInstrument q).bornWeight_nonneg outcome (preSyndromeState q p)
end QEC.Distillation.Triorthogonal.BH12Protocol
