-- Prove2me | solution 1 for SZ.branchDigit_fst_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:49:20.554179+00:00
-- url     : https://prove2.me/submissions/7f1ca7bc-5ec6-47cd-8254-1edb7f48bdc2

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_branchDigit_fst

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {w w' : ℝ} {b b' : Bool} (hb : b ≠ b') :
    (branchDigit w b).1 ≠ (branchDigit w' b').1 := by
  rw [branchDigit_fst, branchDigit_fst]
  cases b <;> cases b' <;> simp_all
end SZ
