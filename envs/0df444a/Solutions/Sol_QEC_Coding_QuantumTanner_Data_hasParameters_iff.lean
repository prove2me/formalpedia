-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.hasParameters_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:08:39.094044+00:00
-- url     : https://prove2.me/submissions/7d5dd7d6-c034-4d87-bd39-a73aecd2fe20

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_QuantumTanner_Core

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
open QEC.Coding.QuantumTanner.Data
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]
namespace QEC.Coding.QuantumTanner.Data
theorem _root_.solution (D : Data G A B Square XBasis ZBasis) (n k d : Nat) :
    D.HasParameters n k d ↔
      n = Fintype.card Square ∧
      k = Module.finrank (ZMod 2) D.chainComplex.middleHomology ∧
      AlgebraicCSSMinimumDistance
        D.chainComplex.firstCoboundaryCheckCode
        D.chainComplex.middleBoundaryCode d := by
  rfl
end QEC.Coding.QuantumTanner.Data
