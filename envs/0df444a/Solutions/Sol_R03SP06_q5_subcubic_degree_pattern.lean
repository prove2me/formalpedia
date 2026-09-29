-- Prove2me | solution 1 for R03SP06.q5_subcubic_degree_pattern
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:48:02.017418+00:00
-- url     : https://prove2.me/submissions/1e7d6401-6614-4205-913f-f33245922322

import Mathlib
import Definitions.Def_cubic_p3_partition_models

/-!
Candidate-only arithmetic packaging for the q=5 residual degree patterns.
-/

namespace R03SP06

open CubicP3Partition

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Deficiency 3-degree has values 0, 1, or 2 when the graph has minimum
 degree one and is subcubic. -/
lemma q5_deficiency_values
    {G : SimpleGraph V}
    (hdeg : ∀ v, 1 ≤ degree G v ∧ degree G v ≤ 3) :
    ∀ v, 3 - degree G v = 0 ∨ 3 - degree G v = 1 ∨
      3 - degree G v = 2 := by
  intro v
  have hv := hdeg v
  omega

/-- The total deficiency is the weighted count of degree-one and degree-two
vertices. -/
lemma q5_weighted_deficiency_identity
    {G : SimpleGraph V}
    (hdeg : ∀ v, 1 ≤ degree G v ∧ degree G v ≤ 3) :
    ∑ v, (3 - degree G v) =
      2 * (Finset.filter (fun v => degree G v = 1) Finset.univ).card +
        (Finset.filter (fun v => degree G v = 2) Finset.univ).card := by
  classical
  have hval := q5_deficiency_values hdeg
  let d : V → Nat := fun v => 3 - degree G v
  let L : Finset V := Finset.filter (fun v => d v = 2) Finset.univ
  let D : Finset V := Finset.filter (fun v => d v = 1) Finset.univ
  have hrewrite : (∑ v, d v) =
      L.sum (fun _ => 2) + D.sum (fun _ => 1) := by
    calc
      ∑ v, d v = ∑ v, (if d v = 2 then 2 else 0) +
          ∑ v, (if d v = 1 then 1 else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v hv
        rcases hval v with h0 | h1 | h2
        · simp [d, h0]
        · simp [d, h1]
        · simp [d, h2]
      _ = L.sum (fun _ => 2) + D.sum (fun _ => 1) := by
        rw [Finset.sum_filter, Finset.sum_filter]
  have hrewrite' :
      (∑ v, (3 - degree G v)) =
        2 * (Finset.filter (fun v => degree G v = 1) Finset.univ).card +
          (Finset.filter (fun v => degree G v = 2) Finset.univ).card := by
    calc
      ∑ v, (3 - degree G v) = ∑ v, d v := by rfl
      _ = L.sum (fun _ => 2) + D.sum (fun _ => 1) := hrewrite
      _ = 2 * L.card + D.card := by simp [Finset.sum_const, Nat.mul_comm]
      _ = 2 * (Finset.filter (fun v => degree G v = 1) Finset.univ).card +
          (Finset.filter (fun v => degree G v = 2) Finset.univ).card := by
        have hL : L = Finset.filter (fun v => degree G v = 1) Finset.univ := by
          ext v
          simp [L, d]
          omega
        have hD : D = Finset.filter (fun v => degree G v = 2) Finset.univ := by
          ext v
          simp [D, d]
          omega
        rw [hL, hD]
  exact hrewrite'


end R03SP06

open R03SP06
open CubicP3Partition
variable {V : Type} [Fintype V] [DecidableEq V]
theorem solution
    {G : SimpleGraph V}
    (hdeg : ∀ v, 1 ≤ degree G v ∧ degree G v ≤ 3)
    (hdef : ∑ v, (3 - degree G v) = 5) :
    2 * (Finset.filter (fun v => degree G v = 1) Finset.univ).card +
        (Finset.filter (fun v => degree G v = 2) Finset.univ).card = 5 ∧
      ((Finset.filter (fun v => degree G v = 1) Finset.univ).card = 0 ∧
          (Finset.filter (fun v => degree G v = 2) Finset.univ).card = 5 ∨
        (Finset.filter (fun v => degree G v = 1) Finset.univ).card = 1 ∧
          (Finset.filter (fun v => degree G v = 2) Finset.univ).card = 3 ∨
        (Finset.filter (fun v => degree G v = 1) Finset.univ).card = 2 ∧
          (Finset.filter (fun v => degree G v = 2) Finset.univ).card = 1) := by
  have hweight := q5_weighted_deficiency_identity hdeg
  rw [hdef] at hweight
  constructor
  · exact hweight.symm
  · omega

