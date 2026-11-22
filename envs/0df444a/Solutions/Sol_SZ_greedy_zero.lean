-- Prove2me | solution 1 for SZ.greedy_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:46:20.332981+00:00
-- url     : https://prove2.me/submissions/4b86979b-8b91-49ea-97a2-81befdef6eb0

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (α : ℝ) : greedy α 0 = 2 := rfl
end SZ
