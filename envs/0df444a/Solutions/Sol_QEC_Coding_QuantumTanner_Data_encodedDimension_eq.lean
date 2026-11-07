-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.encodedDimension_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:08:37.774682+00:00
-- url     : https://prove2.me/submissions/e39715f3-88d0-48fe-bece-a1b693804f5f

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Theorems.Thm_QEC_Coding_ChainComplexData_finrank_middleHomology_eq


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
    D.encodedDimension =
      Dimension D.chainComplex.middleCycleCode -
        Dimension D.chainComplex.middleBoundaryCode := by
  exact D.chainComplex.finrank_middleHomology_eq
end QEC.Coding.QuantumTanner.Data
