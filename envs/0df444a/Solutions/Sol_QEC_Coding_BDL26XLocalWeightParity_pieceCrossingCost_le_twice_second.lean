-- Prove2me | solution 1 for QEC.Coding.BDL26XLocalWeightParity.pieceCrossingCost_le_twice_second
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:41:50.860534+00:00
-- url     : https://prove2.me/submissions/85f46f6c-cc53-44c8-bca1-d29f783fb591

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Theorems.Thm_QEC_Coding_BDL26XLocalWeightParity_bitWeight_le_add

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalWeightParity
open scoped BigOperators
namespace QEC.Coding.BDL26XLocalWeightParity
theorem _root_.solution (a b l r : ZMod 2) :
    pieceCrossingCost a b l r ≤
      bitWeight b + bitWeight b + bitWeight l + bitWeight r := by
  have h := bitWeight_le_add a b
  unfold pieceCrossingCost
  omega
end QEC.Coding.BDL26XLocalWeightParity
