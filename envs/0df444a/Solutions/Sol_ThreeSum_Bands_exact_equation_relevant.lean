-- Prove2me | solution 1 for ThreeSum.Bands.exact_equation_relevant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:04.925479+00:00
-- url     : https://prove2.me/submissions/01a2ce4e-fc8b-4c3a-b93e-3842c66c1d98

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Bands

set_option autoImplicit false
open ThreeSum ThreeSum.Bands
variable {I J K : Type*}
namespace ThreeSum.Bands
theorem _root_.solution
    {alo ahi : I → ℤ} {blo bhi : J → ℤ} {clo chi : K → ℤ}
    {i : I} {j : J} {k : K} {a b c : ℤ}
    (ha : alo i ≤ a ∧ a ≤ ahi i) (hb : blo j ≤ b ∧ b ≤ bhi j)
    (hc : clo k ≤ c ∧ c ≤ chi k) (heq : a + b = c) :
    Relevant alo ahi blo bhi clo chi (i, j, k) := by
  constructor <;> dsimp only <;> omega
end ThreeSum.Bands
