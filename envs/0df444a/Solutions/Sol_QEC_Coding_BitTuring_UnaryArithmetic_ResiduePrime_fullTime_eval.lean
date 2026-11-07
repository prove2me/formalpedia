-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.ResiduePrime.fullTime_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:57:53.939927+00:00
-- url     : https://prove2.me/submissions/ef7c77b4-a10b-4142-97ab-473b717d7dd4

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrimality
import Definitions.Def_QEC_Coding_BitTuring_UnaryResiduePrime
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PrimeLoop_unaryTime_eval


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ResiduePrime
open Turing StateTransition
namespace QEC.Coding.BitTuring.UnaryArithmetic.ResiduePrime
theorem _root_.solution (n : ℕ) : fullTime.eval n =
    (n+1)*(((n+6)^2+1)*(5*(3*(n+6)+3)^2+27*(n+6)+41)+2*(n+6)+3+9*n+21)+4*n+5 := by
  simp only [fullTime,searchTime,callTime,candidateTime,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,PrimeLoop.unaryTime_eval]
  ring
end QEC.Coding.BitTuring.UnaryArithmetic.ResiduePrime
