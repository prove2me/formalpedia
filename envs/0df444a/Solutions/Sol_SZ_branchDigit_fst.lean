-- Prove2me | solution 1 for SZ.branchDigit_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:41:17.40121+00:00
-- url     : https://prove2.me/submissions/2adfac79-bcab-4988-94aa-098de31507b3

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (w : ℝ) (b : Bool) : (branchDigit w b).1 = cond b 2 0 := by
  unfold branchDigit; split_ifs <;> cases b <;> rfl
end SZ
