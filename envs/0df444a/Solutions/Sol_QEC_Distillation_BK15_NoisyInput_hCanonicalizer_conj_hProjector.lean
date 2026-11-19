-- Prove2me | solution 1 for QEC.Distillation.BK15.NoisyInput.hCanonicalizer_conj_hProjector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:06:49.314235+00:00
-- url     : https://prove2.me/submissions/87a6448d-2c18-40cc-8d24-da67a7b69e8e

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_hCanonicalizer_conj_hMagicState
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
theorem _root_.solution (d : HDirection) :
    (hCanonicalizer d).conjOperator (hProjector d) = hProjector hReference := by
  have h := congrArg (fun sigma : DensityOperator QubitSpace => sigma.toOperator)
    (hCanonicalizer_conj_hMagicState d)
  have hReferenceOperator : hMagicState.toOperator = hProjector hReference := by
    rw [← hMagicStateOfReference]
    rfl
  rw [UnitaryTransport.conjDensity_toOperator, hReferenceOperator] at h
  exact h
end QEC.Distillation.BK15.NoisyInput
