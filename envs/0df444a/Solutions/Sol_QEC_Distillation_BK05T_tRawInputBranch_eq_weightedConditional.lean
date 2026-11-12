-- Prove2me | solution 1 for QEC.Distillation.BK05T.tRawInputBranch_eq_weightedConditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:21:57.198384+00:00
-- url     : https://prove2.me/submissions/e55f20ae-4107-48de-9d4b-38b57c9d3c4d

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
namespace QEC.Distillation.BK05T
theorem _root_.solution (epsilon : Real) (word : Fin 2)
    (hpositive : 0 < tInputWeight epsilon word) :
    tRawInputBranch epsilon word =
      (tInputWeight epsilon word : Complex) •
        (tInputConditional epsilon word hpositive).toOperator :=
  rfl
end QEC.Distillation.BK05T
