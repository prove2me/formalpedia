-- Prove2me | solution 1 for QEC.Distillation.BK05T.tInputSquaredOverlap_eq_tInputFidelity_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:29:39.131145+00:00
-- url     : https://prove2.me/submissions/69ff50af-359a-482c-8db7-5bc9aa2c1064

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionSquaredOverlap_nonneg
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tProjector_isSymmetricProjection


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
    tInputSquaredOverlap rho = tInputFidelity rho ^ 2 := by
  unfold tInputSquaredOverlap tInputFidelity tDirectionFidelity projectionFidelity
  rw [Real.sq_sqrt]
  exact projectionSquaredOverlap_nonneg (tProjector tZeroDirection) rho
    (tProjector_isSymmetricProjection tZeroDirection)
end QEC.Distillation.BK05T
