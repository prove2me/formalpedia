-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.ofReal_exp_card_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:58:52.206525+00:00
-- url     : https://prove2.me/submissions/2ff98c29-f4ad-45d3-a637-0b6d30d267dd

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution (Delta cardinality : Nat) :
    ENNReal.ofReal
        (Real.exp (-((Delta : Real) * cardinality / 1000))) =
      (ENNReal.ofReal
        (Real.exp (-(Delta : Real) / 1000))) ^ cardinality := by
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring
end QEC.Coding.FiberBundle.RandomBase
