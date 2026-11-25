-- Prove2me | solution 1 for SZ.branchDigit_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:41:40.490072+00:00
-- url     : https://prove2.me/submissions/b8dba7a7-c04e-4c09-a10d-cff2118446d9

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (w : ℝ) (b : Bool) : EvenDigit (branchDigit w b) := by
  unfold branchDigit EvenDigit; split_ifs <;> cases b <;> simp
end SZ
