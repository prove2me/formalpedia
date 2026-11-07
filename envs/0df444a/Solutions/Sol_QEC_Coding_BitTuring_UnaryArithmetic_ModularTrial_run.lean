-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial.run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:09:03.28898+00:00
-- url     : https://prove2.me/submissions/8728c235-b141-40a4-a7ca-8fa0632d6d67

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularTrial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
open Turing StateTransition
open UnaryOutputEquality
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
theorem _root_.solution (a b r q : ℕ) (hq : 0<q) :
    (fun c => c.bind (TM2.step machine.program))^[steps a b r q]
      (some (machine.init (input a b r q))) =
      some (machine.halt [decide ((a*b)%q=r)]) := by
  let h := executes ModularProduct.machine r ((a*b)%q) (FactorTest.tripleInput a b q)
    (ModularProduct.steps a b q) (ModularProduct.exec a b q hq)
  have hs : h.steps=steps a b r q := by
    change (max ((a*b)%q) r+2)+ModularProduct.steps a b q+(r+1)=
      ModularProduct.steps a b q+r+max ((a*b)%q) r+3
    omega
  rw [←hs]
  exact h.evals_in_steps
end QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
