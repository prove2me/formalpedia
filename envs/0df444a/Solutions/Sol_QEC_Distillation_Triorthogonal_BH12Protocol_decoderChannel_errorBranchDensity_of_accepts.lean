-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.decoderChannel_errorBranchDensity_of_accepts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:51:14.08819+00:00
-- url     : https://prove2.me/submissions/d46a3c94-68c4-4f9d-ab2a-3cdf9ddde425

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_decoderChannel_rankOne_encoded
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_errorBranchState_eq_ambientEncodingIsometry

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
theorem _root_.solution {q : Nat}
    (error : PhysicalError q) (haccept : Accepts error) :
    decoderChannel q (errorBranchDensity error).toOperator =
      (logicalErrorDensity (logicalErrorWord error)).toOperator := by
  rw [errorBranchDensity, DensityOperator.pureDensity_toOperator,
    errorBranchState_eq_ambientEncodingIsometry error haccept,
    decoderChannel_rankOne_encoded, logicalErrorDensity_toOperator]
end QEC.Distillation.Triorthogonal.BH12Protocol
