-- Prove2me | solution 1 for QEC.Distillation.BK05T.tZero_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:29:23.525993+00:00
-- url     : https://prove2.me/submissions/14d2c709-d8ce-4e15-b912-dcb489a9f5d5

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
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
theorem _root_.solution : tZero.toOperator * tZero.toOperator = tZero.toOperator := by
  change tProjector tZeroDirection * tProjector tZeroDirection =
    tProjector tZeroDirection
  exact (tProjector_isSymmetricProjection tZeroDirection).1
end QEC.Distillation.BK05T
