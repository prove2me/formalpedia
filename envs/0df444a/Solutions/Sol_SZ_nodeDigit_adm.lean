-- Prove2me | solution 1 for SZ.nodeDigit_adm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:54:31.44612+00:00
-- url     : https://prove2.me/submissions/a6d4d37a-ba94-4f12-85d6-18c8ddfeebfd

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_evenDigit_pick
import Theorems.Thm_SZ_branchDigit_even
import Theorems.Thm_SZ_branchDigit_adm
import Theorems.Thm_SZ_pick_residual_mem


set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (β : ℕ → Bool) (n : Node) (h0 : 0 ≤ valS n.st)
    (h1 : valS n.st ≤ 3 + 3 * Real.sqrt 3) : Adm n.st (nodeDigit β n) := by
  unfold nodeDigit
  split_ifs with hb
  · exact ⟨branchDigit_even _ _, branchDigit_adm hb.2.2 _⟩
  · exact ⟨evenDigit_pick _, pick_residual_mem h0 h1⟩
end SZ
