-- Prove2me | solution 1 for QEC.Distillation.BK05T.tInputError_diagonalInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:22:42.289402+00:00
-- url     : https://prove2.me/submissions/704ade4a-04cd-4f6e-9835-6175e1a445e5

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Theorems.Thm_QEC_Distillation_BK05T_tInputSquaredOverlap_diagonalInput

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
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    tInputError (tDiagonalInput epsilon hzero hone) = epsilon := by
  rw [tInputError, tInputSquaredOverlap_diagonalInput epsilon hzero hone]
  ring
end QEC.Distillation.BK05T
