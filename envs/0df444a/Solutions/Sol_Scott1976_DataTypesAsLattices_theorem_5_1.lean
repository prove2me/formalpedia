-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:03.346722+00:00
-- url     : https://prove2.me/submissions/943e22b0-791a-4010-bb91-a38a9b4f480f

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
import Theorems.Thm_Scott1976_DataTypesAsLattices_retract_app


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {a : Pomega} (ha : IsClosure a) (n : ℕ) :
    typed (funOf a (e n)) a :=
  (retract_app ha.2 (e n)).symm
end Scott1976.DataTypesAsLattices
