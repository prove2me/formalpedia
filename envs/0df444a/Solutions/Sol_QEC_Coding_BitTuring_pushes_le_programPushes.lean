-- Prove2me | solution 1 for QEC.Coding.BitTuring.pushes_le_programPushes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:59:50.410259+00:00
-- url     : https://prove2.me/submissions/c4655ee0-876a-4cbe-b4a6-5b38058e87ad

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_QEC_Coding_BitTuring_StackGrowth

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring
open Turing
open scoped BigOperators
namespace QEC.Coding.BitTuring
theorem _root_.solution {K Λ σ : Type} [Fintype Λ]
    (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (l : Λ) :
    pushes (M l) ≤ programPushes M :=
  Finset.le_sup (f := fun l => pushes (M l)) (Finset.mem_univ l)
end QEC.Coding.BitTuring
