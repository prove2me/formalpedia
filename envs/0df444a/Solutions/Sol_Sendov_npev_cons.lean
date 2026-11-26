-- Prove2me | solution 1 for Sendov.npev_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:12.456335+00:00
-- url     : https://prove2.me/submissions/53cd53e3-5c97-4848-89b9-baac8ce70906

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (a : ℕ) (p : List ℕ) (b : ℕ) :
    npev (a :: p) b = a + b * npev p b := rfl
end Sendov
