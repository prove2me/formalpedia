-- Prove2me | solution 1 for QEC.Distillation.BK15.NoisyInput.hCanonicalizedDephasedInput_eq_diagonalAResource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:25:43.834206+00:00
-- url     : https://prove2.me/submissions/3b276d3e-7812-4e2c-803a-5babbc175c4f

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_sourceAFramedInput_error_eq_one_sub_hFidelity_sq
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_aBasisDephasing_mapDensity_eq_diagonalAResource
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


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
theorem _root_.solution
    (rho : DensityOperator QubitSpace) (hpositive : 0 < 1 - hFidelity rho ^ 2)
    (hleHalf : 1 - hFidelity rho ^ 2 ≤ 1 / 2) :
    hCanonicalizedDephasedInput rho =
      diagonalAResource (hCanonicalizedInputEpsilon rho hpositive hleHalf) := by
  unfold hCanonicalizedDephasedInput
  apply aBasisDephasing_mapDensity_eq_diagonalAResource
  exact (sourceAFramedInput_error_eq_one_sub_hFidelity_sq rho).symm
end QEC.Distillation.BK15.NoisyInput
