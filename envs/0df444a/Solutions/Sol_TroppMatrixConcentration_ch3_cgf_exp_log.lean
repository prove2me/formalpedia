-- Prove2me | solution 1 for TroppMatrixConcentration.ch3_cgf_exp_log
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:21:55.449843+00:00
-- url     : https://prove2.me/submissions/4810e4c5-edbd-4115-812d-1b346dfd73e4

import Definitions.Def_TroppMatrixConcentration_spectral

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
set_option autoImplicit false
open TroppMatrixConcentration

theorem solution {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    (matrixExp A).PosDef ∧ matrixLog (matrixExp A) = A := by
  constructor
  · rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint]
    apply Matrix.IsStrictlyPositive.posDef
    exact (cfc_isStrictlyPositive_iff Real.exp A (by fun_prop) hA.isSelfAdjoint).mpr
      (fun x _ => Real.exp_pos x)
  · exact CFC.log_exp A hA.isSelfAdjoint
