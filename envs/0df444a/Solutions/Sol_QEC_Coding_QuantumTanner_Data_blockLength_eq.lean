-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.blockLength_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:08:50.464637+00:00
-- url     : https://prove2.me/submissions/3605dc74-f25e-452d-9d73-25eba9c76bd4

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
theorem _root_.solution (D : Data G A B Square XBasis ZBasis) :
    D.blockLength = Fintype.card Square :=
  rfl
end QEC.Coding.QuantumTanner.Data
