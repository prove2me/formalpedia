-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TRecurrence_eq_oddsFormula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:54:48.493818+00:00
-- url     : https://prove2.me/submissions/403095b6-e10e-4f05-9a7c-70588b9788f0

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
import Theorems.Thm_QEC_Distillation_BK05T_bk05TOdds_nonneg

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
    bk05TRecurrence epsilon =
      (bk05TOdds epsilon ^ 5 + 5 * bk05TOdds epsilon ^ 2) /
        (1 + 5 * bk05TOdds epsilon ^ 2 +
          5 * bk05TOdds epsilon ^ 3 + bk05TOdds epsilon ^ 5) := by
  have hsuccess := bk05T_successProbability_pos epsilon hzero hhalf
  have hcomplement : 1 - epsilon ≠ 0 := by linarith
  have hodds_nonneg := bk05TOdds_nonneg epsilon hzero hhalf
  have hodds_denom :
      0 < 1 + 5 * bk05TOdds epsilon ^ 2 +
        5 * bk05TOdds epsilon ^ 3 + bk05TOdds epsilon ^ 5 := by
    positivity
  unfold bk05TRecurrence bk05TOdds fiveQubitSuccessProbability
    fiveQubitRawTZeroCoefficient fiveQubitRawTOneCoefficient
  field_simp [hsuccess.ne', hcomplement, hodds_denom.ne']
  ring
end QEC.Distillation.BK05T
