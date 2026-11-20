-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TIteration_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:46:41.651683+00:00
-- url     : https://prove2.me/submissions/1bcaa105-7af3-4d6a-96c1-a4dfb1ce745f

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
namespace QEC.Distillation.BK05T
theorem _root_.solution (epsilon : Real) (rounds : Nat) :
    bk05TIteration epsilon (rounds + 1) =
      bk05TRecurrence (bk05TIteration epsilon rounds) := by
  rw [bk05TIteration, bk05TIteration, Function.iterate_succ_apply']
end QEC.Distillation.BK05T
