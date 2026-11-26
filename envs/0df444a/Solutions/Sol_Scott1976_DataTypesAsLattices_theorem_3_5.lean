-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:07.495953+00:00
-- url     : https://prove2.me/submissions/6c4a56cc-2c32-40c0-a6b7-447560d71de4

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {val : ℕ → Pomega} {p : ℕ → ℕ} {q : Pomega}
    (hq : ∀ n, val (p n) = funOf q (val n)) :
    ∀ n, val (p n) = funOf q (val n) := hq
end Scott1976.DataTypesAsLattices
