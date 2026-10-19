-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P01.partialTranspose_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:14:06.412697+00:00
-- url     : https://prove2.me/submissions/ad7ca7f8-c985-41c3-a16c-1894af3a3b1d

import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability

open scoped ComplexOrder
open QAlgorithms.Entanglement

theorem solution
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ) (density : QAlgorithms.IsDensityMatrix rho) :
    (partialTransposeFirst rho).IsHermitian := by
  ext p q
  exact congrFun (congrFun density.1.isHermitian (q.1, p.2)) (p.1, q.2)
