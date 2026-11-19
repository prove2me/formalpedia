-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.sourceAReturnedH_referenceSquaredOverlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:30:12.60246+00:00
-- url     : https://prove2.me/submissions/00a10071-d399-4748-8ef5-8a4bbdcbaf04

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_sourceA0Transport_conj_hReference_projector
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionSquaredOverlap_conjDensity

section
noncomputable section
namespace QEC
namespace Distillation
namespace BK15
namespace Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
namespace BK15SemanticSchedule
end BK15SemanticSchedule
private theorem sourceA0Transport_symm_conj_aPositive :
    sourceA0Transport.symm.conjOperator (aBasisProjector .positive) =
      hProjector hReference := by
  calc
    sourceA0Transport.symm.conjOperator (aBasisProjector .positive) =
        sourceA0Transport.symm.conjOperator
          (sourceA0Transport.conjOperator (hProjector hReference)) := by
            rw [sourceA0Transport_conj_hReference_projector]
    _ = hProjector hReference :=
      sourceA0Transport.symm_conjOperator_conjOperator _
end Threshold
end BK15
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
namespace QEC.Distillation.BK15.Threshold
theorem _root_.solution
    (sigma : DensityOperator QubitSpace) :
    projectionSquaredOverlap (hProjector hReference)
        (sourceA0Transport.symm.conjDensity sigma) =
      aInputSquaredOverlap sigma := by
  unfold aInputSquaredOverlap
  calc
    projectionSquaredOverlap (hProjector hReference)
        (sourceA0Transport.symm.conjDensity sigma) =
      projectionSquaredOverlap
        (sourceA0Transport.symm.conjOperator (aBasisProjector .positive))
        (sourceA0Transport.symm.conjDensity sigma) := by
          rw [sourceA0Transport_symm_conj_aPositive]
    _ = projectionSquaredOverlap (aBasisProjector .positive) sigma :=
      projectionSquaredOverlap_conjDensity sourceA0Transport.symm
        (aBasisProjector .positive) sigma
end QEC.Distillation.BK15.Threshold
