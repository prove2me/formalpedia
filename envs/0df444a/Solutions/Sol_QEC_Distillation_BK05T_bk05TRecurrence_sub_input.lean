-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TRecurrence_sub_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:42:33.297128+00:00
-- url     : https://prove2.me/submissions/1a8d2acd-d28a-4325-a6f6-0f08421cec3c

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
    bk05TRecurrence epsilon - epsilon =
      -(epsilon * (1 - epsilon) * (1 - 2 * epsilon) *
          bk05TThresholdPolynomial epsilon) /
        (6 * fiveQubitSuccessProbability epsilon) := by
  have hsuccess := bk05T_successProbability_pos epsilon hzero hhalf
  unfold bk05TRecurrence
  field_simp [hsuccess.ne']
  unfold bk05TThresholdPolynomial fiveQubitSuccessProbability
    fiveQubitRawTZeroCoefficient fiveQubitRawTOneCoefficient
  ring
end QEC.Distillation.BK05T
