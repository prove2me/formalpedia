-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_5_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:19.989589+00:00
-- url     : https://prove2.me/submissions/244103c7-d4e4-43ce-b456-b15d7354ac71

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {a b : Pomega} (_ha : IsClosure a) (_hb : IsClosure b) :
    boxTensor a b = graph (fun u =>
      squarePair (funOf a (squareFst u)) (funOf b (squareSnd u))) :=
  rfl
end Scott1976.DataTypesAsLattices
