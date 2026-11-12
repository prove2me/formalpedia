-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.rawEndpoint_eq_zero_of_weight_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:26:55.1036+00:00
-- url     : https://prove2.me/submissions/8f8516ab-14b0-4869-ad9b-1f196e11eafd

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_eq_zero_of_bornWeight_eq_zero


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
    (outcome : DistillationOutcome) (hzero : endpointWeight q p outcome = 0) :
    rawEndpoint q p outcome = 0 :=
  (protocolSyndromeInstrument q).branchOperator_eq_zero_of_bornWeight_eq_zero
    outcome (preSyndromeState q p) hzero
end QEC.Distillation.Triorthogonal.BH12Protocol
