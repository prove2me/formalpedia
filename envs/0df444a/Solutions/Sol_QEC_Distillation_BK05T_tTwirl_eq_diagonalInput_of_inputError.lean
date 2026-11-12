-- Prove2me | solution 1 for QEC.Distillation.BK05T.tTwirl_eq_diagonalInput_of_inputError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:37:40.109199+00:00
-- url     : https://prove2.me/submissions/de603d9c-344b-425c-9491-ed97e48f4bf6

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Theorems.Thm_QEC_Distillation_BK05T_tTwirlBloch_eq_tDiagonalBloch_of_inputError
import Theorems.Thm_QEC_Distillation_BK05T_tTwirl_eq_diagonalInput_of_bloch
import Theorems.Thm_QEC_Distillation_OneQubitMagic_density_toOperator_eq_blochProjector


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
    tTwirl rho = tDiagonalInput (tInputError rho) hzero hone := by
  exact tTwirl_eq_diagonalInput_of_bloch rho (densityBloch rho)
    (density_toOperator_eq_blochProjector rho) (tInputError rho) hzero hone
    (tTwirlBloch_eq_tDiagonalBloch_of_inputError rho (densityBloch rho)
      (density_toOperator_eq_blochProjector rho))
end QEC.Distillation.BK05T
