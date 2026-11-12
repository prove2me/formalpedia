-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.resourceDecodedRun_successProbability_noisyResources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:06:05.83204+00:00
-- url     : https://prove2.me/submissions/3fec5ff8-5ad6-4b1b-8ef7-9ac818483d60

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_resourceAcceptedWeight_noisyResources_eq_rawSuccessMass

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
theorem _root_.solution (q : Nat)
    (p : ErrorParameter) :
    (resourceDecodedRun q (noisyResources q p)).successProbability =
      rawSuccessMass q p :=
  resourceAcceptedWeight_noisyResources_eq_rawSuccessMass q p
end QEC.Distillation.Triorthogonal.BH12Protocol
