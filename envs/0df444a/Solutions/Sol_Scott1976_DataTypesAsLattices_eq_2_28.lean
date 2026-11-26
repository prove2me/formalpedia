-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.eq_2_28
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:39.031283+00:00
-- url     : https://prove2.me/submissions/6fb12a7b-d4fe-4196-a3fd-06ea3e402c4c

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_4


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {g : Pomega → Pomega → Pomega}
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) (x : Pomega) :
    fix (g x) = g x (fix (g x)) :=
  (theorem_1_4 (hgy x)).1.symm
end Scott1976.DataTypesAsLattices
