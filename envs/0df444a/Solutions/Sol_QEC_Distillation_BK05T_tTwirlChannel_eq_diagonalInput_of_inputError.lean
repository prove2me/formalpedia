-- Prove2me | solution 1 for QEC.Distillation.BK05T.tTwirlChannel_eq_diagonalInput_of_inputError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:23:03.576229+00:00
-- url     : https://prove2.me/submissions/66c3aeee-7e89-49f6-ad42-a04836648059

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Theorems.Thm_QEC_Distillation_BK05T_tTwirlChannel_mapDensity
import Theorems.Thm_QEC_Distillation_BK05T_tTwirl_eq_diagonalInput_of_inputError

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
    (rho : DensityOperator QubitSpace)
    (hzero : 0 ≤ tInputError rho) (hone : tInputError rho ≤ 1) :
    tTwirlChannel.mapDensity rho =
      tDiagonalInput (tInputError rho) hzero hone := by
  rw [tTwirlChannel_mapDensity,
    tTwirl_eq_diagonalInput_of_inputError rho hzero hone]
end QEC.Distillation.BK05T
