-- Prove2me | solution 1 for Problem97.CGN.card_witnessedPairsAt_le_left
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:05:47.972526+00:00
-- url     : https://prove2.me/submissions/59cb6b7f-201e-42e0-839d-be70c5f56834

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN:7519:8831. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Fin

section Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN

open Problem97 Problem97.CGN

/- Fragment from Erdos9796Proof.P97.CGN.CGN; source SHA-256 9f1ccd7df30637d7fbdf412fb40177dedb5193c45ec2993df86f137cbd34ffb7 -/


/-!
# CGN7: indexed cap-side witness matching scaffold

This file records the CGN7-local indexed witness relation requested by the
updated counterexample-card-ge-nine prose.  The geometry that produces the
one-sided injectivity hypotheses lives in the CGN6 lemmas; this module only
packages the ordered-cap interface and the partial-matching counting shell.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace
open Finset








variable {m : ℕ}





























/-- Membership in `WitnessedPairsAt` is exactly the indexed witness relation. -/
@[simp] theorem Problem97.CGN.mem_WitnessedPairsAt_iff {m : ℕ} {L : OrderedCap m} {j : Fin m}
    {p : Fin m × Fin m} :
    p ∈ WitnessedPairsAt L j ↔ WitnessesCapEdgeAt L j p.1 p.2 := by
  classical
  unfold WitnessedPairsAt
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩


theorem solution {m : ℕ} (L : OrderedCap m) (j : Fin m)
    (hleft : ∀ {r s t : Fin m}, WitnessesCapEdgeAt L j r s →
      WitnessesCapEdgeAt L j r t → s = t) :
    (WitnessedPairsAt L j).card ≤ j.val := by
  have hcard : (WitnessedPairsAt L j).card ≤ (Finset.Ico 0 j.val).card := by
    refine Finset.card_le_card_of_injOn (fun p : Fin m × Fin m => p.1.val) ?_ ?_
    · intro n hn
      change n ∈ WitnessedPairsAt L j at hn
      have hnrel : WitnessesCapEdgeAt L j n.1 n.2 := (mem_WitnessedPairsAt_iff).mp hn
      have hlt : n.1.val < j.val := Fin.lt_def.mp hnrel.1
      change n.1.val ∈ Finset.Ico 0 j.val
      rw [Finset.mem_Ico]
      exact ⟨Nat.zero_le _, hlt⟩
    · intro p hp q hq hEq
      change p ∈ WitnessedPairsAt L j at hp
      change q ∈ WitnessedPairsAt L j at hq
      have hEqFin : p.1 = q.1 := Fin.ext hEq
      have hpw : WitnessesCapEdgeAt L j p.1 p.2 := (mem_WitnessedPairsAt_iff).mp hp
      have hqw : WitnessesCapEdgeAt L j p.1 q.2 := by
        simpa [hEqFin] using (mem_WitnessedPairsAt_iff).mp hq
      have hsecond : p.2 = q.2 := hleft hpw hqw
      exact Prod.ext hEqFin hsecond
  simpa [Nat.card_Ico] using hcard

























-- The next two CGN7c theorems depend on the missing CGN6e indexed-witness
-- bridge.  Stop here rather than inventing that geometry.

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN
