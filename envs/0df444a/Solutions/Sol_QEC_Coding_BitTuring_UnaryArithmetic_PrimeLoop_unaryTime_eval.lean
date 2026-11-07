-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop.unaryTime_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:39:24.78622+00:00
-- url     : https://prove2.me/submissions/5be1d4f7-e564-4f57-9c7f-ff6a4943aef8

import Definitions.Def_QEC_Coding_BitTuring_UnaryFactorTrial
import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_QEC_Coding_BitTuring_UnaryPrimality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop
theorem _root_.solution (n : ℕ) : unaryTime.eval n =
    ((n+6)^2+1)*(5*(3*(n+6)+3)^2+27*(n+6)+41)+2*(n+6)+3 := by
  simp only [unaryTime,time,FactorTrial.trialTime,FactorTest.time,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_pow,Polynomial.eval_one,
    Polynomial.eval_X,Polynomial.eval_C]
  ring
end QEC.Coding.BitTuring.UnaryArithmetic.PrimeLoop
