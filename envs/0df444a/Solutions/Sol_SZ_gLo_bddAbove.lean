-- Prove2me | solution 1 for SZ.gLo_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:53.934823+00:00
-- url     : https://prove2.me/submissions/20f7d4a6-f6e3-4024-8d41-90d0bc4d528a

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
import Theorems.Thm_P2M_SZ_gLo_lt_gHi__a0fcea13b7a8

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (hα : 3 ≤ α) : BddAbove (Set.range (gLo α)) := by
  refine ⟨gHi α 0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (gLo_lt_gHi' hα n 0).le
end SZ
