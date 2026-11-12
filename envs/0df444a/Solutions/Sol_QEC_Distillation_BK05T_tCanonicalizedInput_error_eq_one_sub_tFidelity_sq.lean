-- Prove2me | solution 1 for QEC.Distillation.BK05T.tCanonicalizedInput_error_eq_one_sub_tFidelity_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:46:10.362948+00:00
-- url     : https://prove2.me/submissions/414703de-d89f-4b11-9c14-ae6f7b3955d2

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Theorems.Thm_QEC_Distillation_BK05T_tInputError_eq_one_sub_tInputFidelity_sq
import Theorems.Thm_QEC_Distillation_BK05T_tCanonicalizedInput_tInputFidelity

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
    tInputError (tCanonicalizedInput rho) = 1 - tFidelity rho ^ 2 := by
  rw [tInputError_eq_one_sub_tInputFidelity_sq,
    tCanonicalizedInput_tInputFidelity]
end QEC.Distillation.BK05T
