-- Prove2me | solution 1 for QEC.Coding.BDL26XLocalWeightParity.bitWeight_le_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:38:51.234012+00:00
-- url     : https://prove2.me/submissions/e499a6d1-c786-4d7c-aff1-52ecc0214797

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26XLocalWeightParity
open scoped BigOperators
namespace QEC.Coding.BDL26XLocalWeightParity
theorem _root_.solution (a b : ZMod 2) :
    bitWeight a ≤ bitWeight (a + b) + bitWeight b := by
  fin_cases a <;> fin_cases b <;> decide
end QEC.Coding.BDL26XLocalWeightParity
