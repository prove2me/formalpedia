-- Prove2me | solution 1 for QEC.Distillation.BK05T.tTwirlChannel_eq_diagonalInput_of_bloch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:23:00.298211+00:00
-- url     : https://prove2.me/submissions/cc964b86-cf44-494e-8232-16abc9d911a6

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Theorems.Thm_QEC_Distillation_BK05T_tTwirlChannel_mapDensity
import Theorems.Thm_QEC_Distillation_BK05T_tTwirl_eq_diagonalInput_of_bloch

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
    (rho : DensityOperator QubitSpace) (r : PauliAxis → Real)
    (hrho : rho.toOperator = blochProjector r)
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (hdiagonal : tTwirlBloch r = tDiagonalBloch epsilon) :
    tTwirlChannel.mapDensity rho = tDiagonalInput epsilon hzero hone := by
  rw [tTwirlChannel_mapDensity,
    tTwirl_eq_diagonalInput_of_bloch rho r hrho epsilon hzero hone hdiagonal]
end QEC.Distillation.BK05T
