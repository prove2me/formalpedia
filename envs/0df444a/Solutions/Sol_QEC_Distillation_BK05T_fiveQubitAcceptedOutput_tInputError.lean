-- Prove2me | solution 1 for QEC.Distillation.BK05T.fiveQubitAcceptedOutput_tInputError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:53:59.233096+00:00
-- url     : https://prove2.me/submissions/79fc0d3a-1aee-4e98-8db5-2fb738492906

import Theorems.Thm_QEC_Distillation_BK05T_fiveQubitAcceptedOutput_eq_diagonalInput
import Theorems.Thm_QEC_Distillation_BK05T_tInputError_diagonalInput


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
    tInputError (fiveQubitAcceptedOutput epsilon hzero (by linarith)) =
      bk05TRecurrence epsilon := by
  rw [fiveQubitAcceptedOutput_eq_diagonalInput epsilon hzero hhalf]
  exact tInputError_diagonalInput _ _ _
end QEC.Distillation.BK05T
