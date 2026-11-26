-- Prove2me | solution 1 for Sendov.T2_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:00:39.875441+00:00
-- url     : https://prove2.me/submissions/94ecffca-5941-47c2-9fb7-8432fe47991f

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
import Theorems.Thm_Sendov_T2_step

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : T2 n α ≤ T2 101 α := by
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact (T2_step hm hα hα').trans ih
end Sendov
