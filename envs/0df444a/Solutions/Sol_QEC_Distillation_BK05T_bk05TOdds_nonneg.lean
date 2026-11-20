-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TOdds_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:47:58.067975+00:00
-- url     : https://prove2.me/submissions/9513b425-6a3c-4637-a066-2a7e41c6acb5

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
theorem _root_.solution
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    0 <= bk05TOdds epsilon := by
  exact div_nonneg hzero (by linarith)
end QEC.Distillation.BK05T
