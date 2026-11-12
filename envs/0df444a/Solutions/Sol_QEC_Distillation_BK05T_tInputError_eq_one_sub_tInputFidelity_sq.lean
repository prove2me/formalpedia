-- Prove2me | solution 1 for QEC.Distillation.BK05T.tInputError_eq_one_sub_tInputFidelity_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:32:52.913766+00:00
-- url     : https://prove2.me/submissions/6cbb8f3f-7132-4f9f-bc8e-cee810d63540

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Theorems.Thm_QEC_Distillation_BK05T_tInputSquaredOverlap_eq_tInputFidelity_sq

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
namespace QEC.Distillation.BK05T
theorem _root_.solution
    (rho : DensityOperator QubitSpace) :
    tInputError rho = 1 - tInputFidelity rho ^ 2 := by
  rw [tInputError, tInputSquaredOverlap_eq_tInputFidelity_sq]
end QEC.Distillation.BK05T
