-- Prove2me | solution 1 for R03SP06.q3_subcubic_degree_pattern
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:04:11.663758+00:00
-- url     : https://prove2.me/submissions/7b3798f3-cbc3-4e4c-9a87-03f5ebade0b8

import Mathlib
import Definitions.Def_cubic_p3_partition_models

/-!
Candidate-only arithmetic packaging for the q=3 residual degree pattern.
-/

namespace R03SP06

open CubicP3Partition

variable {V : Type} [Fintype V] [DecidableEq V]

lemma sum_binary_eq_filter_card
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


end R03SP06

open R03SP06
open CubicP3Partition
variable {V : Type} [Fintype V] [DecidableEq V]
theorem solution
    {G : SimpleGraph V}
    (hdeg : ∀ v, 2 ≤ degree G v ∧ degree G v ≤ 3)
    (hdef : ∑ v, (3 - degree G v) = 3) :
    (Finset.filter (fun v => degree G v = 2) Finset.univ).card = 3 ∧
      ∀ v, degree G v = 2 ∨ degree G v = 3 := by
  have hbin : ∀ v, 3 - degree G v = 0 ∨ 3 - degree G v = 1 := by
    intro v
    have hv := hdeg v
    omega
  have hcount := sum_binary_eq_filter_card hbin hdef
  have hfilter :
      Finset.filter (fun v => 3 - degree G v = 1) Finset.univ =
        Finset.filter (fun v => degree G v = 2) Finset.univ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  constructor
  · rw [← hfilter]
    exact hcount
  · intro v
    have hv := hdeg v
    omega

