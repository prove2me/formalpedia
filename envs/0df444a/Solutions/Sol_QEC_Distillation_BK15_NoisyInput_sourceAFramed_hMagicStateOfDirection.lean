-- Prove2me | solution 1 for QEC.Distillation.BK15.NoisyInput.sourceAFramed_hMagicStateOfDirection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:12:12.07201+00:00
-- url     : https://prove2.me/submissions/a5a4670b-dbd8-4b23-b3f7-23093855a13a

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_hCanonicalizer_conj_hMagicState

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
    sourceA0Transport.conjDensity
      ((hCanonicalizer d).conjDensity (hMagicStateOfDirection d)) = aZeroDensity := by
  rw [hCanonicalizer_conj_hMagicState]
  rfl
end QEC.Distillation.BK15.NoisyInput
