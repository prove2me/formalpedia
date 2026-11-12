-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.bh12MagicStateDistillationProtocol_successfulOutputError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:15:53.026566+00:00
-- url     : https://prove2.me/submissions/60bfe419-f812-441b-a8ad-18e9f74eaa69

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_bh12ABasisOutputError_acceptedOutput

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
    (p : ErrorParameter) (a : OddRow q) (hsuccess : 0 < rawSuccessMass q p) :
    (bh12MagicStateDistillationProtocol q p a hsuccess).successfulOutputError =
      decodedMarginalError q p hsuccess a := by
  exact bh12ABasisOutputError_acceptedOutput q p hsuccess a
end QEC.Distillation.Triorthogonal.BH12Protocol
