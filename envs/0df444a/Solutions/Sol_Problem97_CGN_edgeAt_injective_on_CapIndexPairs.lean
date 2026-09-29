-- Prove2me | solution 1 for Problem97.CGN.edgeAt_injective_on_CapIndexPairs
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:05:45.009502+00:00
-- url     : https://prove2.me/submissions/27f46716-d681-4307-ba98-17a3f93772c5

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN:13744:15343. -/
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









































/-- An index pair belongs to `CapIndexPairs m` exactly when it is oriented
strictly increasingly. -/
@[simp] theorem Problem97.CGN.mem_CapIndexPairs {m : ℕ} {p : Fin m × Fin m} :
    p ∈ CapIndexPairs m ↔ p.1 < p.2 := by
  simp [CapIndexPairs]






theorem solution {m : ℕ} {L : OrderedCap m}
    {p q : Fin m × Fin m} (hp : p ∈ CapIndexPairs m) (hq : q ∈ CapIndexPairs m)
    (heq : edgeAt L p.1 p.2 = edgeAt L q.1 q.2) :
    p = q := by
  have hp_lt : p.1 < p.2 := (mem_CapIndexPairs.mp hp)
  have hq_lt : q.1 < q.2 := (mem_CapIndexPairs.mp hq)
  have hp1mem : L.points p.1 ∈ edgeAt L q.1 q.2 := by
    have hmem : L.points p.1 ∈ edgeAt L p.1 p.2 := by simp [edgeAt]
    rw [heq] at hmem
    exact hmem
  have hp2mem : L.points p.2 ∈ edgeAt L q.1 q.2 := by
    have hmem : L.points p.2 ∈ edgeAt L p.1 p.2 := by simp [edgeAt]
    rw [heq] at hmem
    exact hmem
  simp [edgeAt] at hp1mem hp2mem
  have hp1idx : p.1 = q.1 ∨ p.1 = q.2 := by
    rcases hp1mem with hp1mem | hp1mem
    · exact Or.inl (L.injective hp1mem)
    · exact Or.inr (L.injective hp1mem)
  have hp2idx : p.2 = q.1 ∨ p.2 = q.2 := by
    rcases hp2mem with hp2mem | hp2mem
    · exact Or.inl (L.injective hp2mem)
    · exact Or.inr (L.injective hp2mem)
  rcases hp1idx with hp1idx | hp1idx
  · rcases hp2idx with hp2idx | hp2idx
    · exfalso
      have hlt : q.1 < q.1 := by simpa [hp1idx, hp2idx] using hp_lt
      exact (lt_irrefl _ hlt)
    · exact Prod.ext hp1idx hp2idx
  · rcases hp2idx with hp2idx | hp2idx
    · exfalso
      have hlt : q.2 < q.1 := by simpa [hp1idx, hp2idx] using hp_lt
      exact (lt_irrefl _ (lt_trans hlt hq_lt))
    · exfalso
      have hlt : q.2 < q.2 := by simpa [hp1idx, hp2idx] using hp_lt
      exact (lt_irrefl _ hlt)









-- The next two CGN7c theorems depend on the missing CGN6e indexed-witness
-- bridge.  Stop here rather than inventing that geometry.

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN
