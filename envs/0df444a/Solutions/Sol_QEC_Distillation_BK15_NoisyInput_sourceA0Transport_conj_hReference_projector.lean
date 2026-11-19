-- Prove2me | solution 1 for QEC.Distillation.BK15.NoisyInput.sourceA0Transport_conj_hReference_projector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:18:29.697476+00:00
-- url     : https://prove2.me/submissions/77d95369-d7c6-4a02-b37f-a18bfba271db

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_aBasisProjector_positive_eq_aZeroDensity_toOperator
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Distillation
namespace BK15
namespace NoisyInput
open Semantics Semantics.Qubit
open OneQubitMagic
open Coding.PauliSymplectic
open scoped BigOperators TensorProduct
universe u v w
attribute [local instance 100] Fintype.ofFinite
private theorem densityOperator_ext
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
private theorem hMagicStateOfReference :
    hMagicStateOfDirection hReference = hMagicState := by
  apply densityOperator_ext
  change blochProjector (hBlochOfDirection hReference) = blochProjector hBloch
  congr 1
  funext axis
  fin_cases axis <;>
    norm_num [hReference, hBlochOfDirection, hBloch, signedCoordinateValue]
namespace BK15Epsilon
end BK15Epsilon
section
set_option maxRecDepth 65536
end
end NoisyInput
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
open QEC.Distillation.BK15.NoisyInput
open Semantics Semantics.Qubit
open OneQubitMagic
open Coding.PauliSymplectic
open scoped BigOperators TensorProduct
universe u v w
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.BK15.NoisyInput
theorem _root_.solution :
    sourceA0Transport.conjOperator (hProjector hReference) =
      aBasisProjector .positive := by
  have hReferenceOperator : hMagicState.toOperator = hProjector hReference := by
    rw [← hMagicStateOfReference]
    rfl
  calc
    sourceA0Transport.conjOperator (hProjector hReference) =
        sourceA0Transport.conjOperator hMagicState.toOperator := by
      rw [hReferenceOperator]
    _ = sourceA0Density.toOperator := by
      rw [sourceA0Density, UnitaryTransport.conjDensity_toOperator]
    _ = aZeroDensity.toOperator := rfl
    _ = aBasisProjector .positive :=
      aBasisProjector_positive_eq_aZeroDensity_toOperator.symm
end QEC.Distillation.BK15.NoisyInput
