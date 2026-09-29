-- Prove2me | solution 1 for R03SP06.sum_binary_eq_filter_card
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:48:03.391953+00:00
-- url     : https://prove2.me/submissions/3f53558f-7627-43ca-bccb-2e2c1c476f93

import Mathlib
import Definitions.Def_cubic_p3_partition_models

/-!
Candidate-only arithmetic packaging for the q=3 residual degree pattern.
-/

namespace R03SP06

open CubicP3Partition

variable {V : Type} [Fintype V] [DecidableEq V]


end R03SP06

open R03SP06
open CubicP3Partition
variable {V : Type} [Fintype V] [DecidableEq V]
theorem solution
    {d : V → Nat}
    (hbin : ∀ v, d v = 0 ∨ d v = 1)
    (hsum : ∑ v, d v = 3) :
    (Finset.filter (fun v => d v = 1) Finset.univ).card = 3 := by
  have hrewrite :
      (∑ v, d v) =
        (Finset.filter (fun v => d v = 1) Finset.univ).sum (fun _ => 1) := by
    calc
      ∑ v, d v = ∑ v, if d v = 1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        rcases hbin v with h0 | h1
        · simp [h0]
        · simp [h1]
      _ = (Finset.filter (fun v => d v = 1) Finset.univ).sum (fun _ => 1) := by
        rw [Finset.sum_filter]
  rw [hsum] at hrewrite
  simpa using hrewrite.symm

