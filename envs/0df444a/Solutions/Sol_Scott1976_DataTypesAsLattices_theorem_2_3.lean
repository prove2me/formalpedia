-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:09.769795+00:00
-- url     : https://prove2.me/submissions/51c85fb8-ed4a-48f8-8bc5-09ec3553be03

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_curry2_app

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y)) :
    ∃ u, ∀ x y, funOf (funOf u x) y = f x y :=
  ⟨curry2 f hfx hfy, curry2_app f hfx hfy⟩
end Scott1976.DataTypesAsLattices
