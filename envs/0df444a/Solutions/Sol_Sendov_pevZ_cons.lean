-- Prove2me | solution 1 for Sendov.pevZ_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:54:11.408805+00:00
-- url     : https://prove2.me/submissions/9cd9f0cb-44fe-4f2b-957b-579ac6708658

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (a : ℤ) (p : List ℤ) (b : ℤ) :
    pevZ (a :: p) b = a + b * pevZ p b := rfl
end Sendov
