-- Prove2me | solution 1 for QEC.Coding.LiftedProduct.rate_le_finrank_middleHomology_of_endpoint_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:46:34.521149+00:00
-- url     : https://prove2.me/submissions/3a32b715-b3d2-40c6-90f2-90f50ece47aa

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Theorems.Thm_QEC_Coding_LiftedProduct_card_qubitIndex_le_finrank_middleHomology_add_endpoints

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v
namespace QEC.Coding.LiftedProduct
theorem _root_.solution
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) (rate : ℝ)
    (hEndpoints :
      (Fintype.card (C0Index aRow bRow G) : ℝ) +
        (Fintype.card (C2Index aCol bCol G) : ℝ) ≤
        (1 - rate) * Fintype.card (QubitIndex aRow aCol bRow bCol G)) :
    rate * Fintype.card (QubitIndex aRow aCol bRow bCol G) ≤
      (Module.finrank F (chainComplex D).middleHomology : ℝ) := by
  have hCells :
      (Fintype.card (QubitIndex aRow aCol bRow bCol G) : ℝ) ≤
        (Module.finrank F (chainComplex D).middleHomology : ℝ) +
          Fintype.card (C0Index aRow bRow G) +
          Fintype.card (C2Index aCol bCol G) := by
    exact_mod_cast card_qubitIndex_le_finrank_middleHomology_add_endpoints D
  nlinarith
end QEC.Coding.LiftedProduct
