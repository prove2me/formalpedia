-- Prove2me | solution 1 for TroppMatrixConcentration.ch8_log_operator_monotone
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:44:30.653469+00:00
-- url     : https://prove2.me/submissions/ae447025-f42c-48ea-9922-bd5f53949aba

import Definitions.Def_TroppMatrixConcentration_ch8_entropy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open TroppMatrixConcentration
set_option autoImplicit false

theorem solution {d : ℕ} [NeZero d]
    (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosDef) (hH : H.PosDef)
    (hAH : loewnerLE A H) :
    loewnerLE (matrixLog A) (matrixLog H) := by
  exact CFC.log_monotoneOn hA.isStrictlyPositive hH.isStrictlyPositive hAH
