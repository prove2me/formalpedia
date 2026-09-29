-- Prove2me | solution 1 for Problem97.CGN.capPairApexes_mem_edgeAt_packet
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:05:46.533051+00:00
-- url     : https://prove2.me/submissions/2e0bba97-fe81-4d03-82aa-d06716c60a1d

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN:16275:17207. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_Dumitrescu_L6
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
























































theorem solution {m : ℕ} {L : OrderedCap m}
    {A : Finset ℝ²} {r s : Fin m} {a : ℝ²}
    (ha : a ∈ Problem97.Dumitrescu.capPairApexes A (edgeAt L r s)) :
    a ∈ A ∧ a ≠ L.points r ∧ a ≠ L.points s ∧
      dist a (L.points r) = dist a (L.points s) := by
  classical
  rw [Problem97.Dumitrescu.capPairApexes] at ha
  rw [Finset.mem_filter] at ha
  rcases ha with ⟨haA, ha⟩
  rcases ha with ⟨haNot, rho, hrho⟩
  have hnotr : a ≠ L.points r := by
    intro h
    apply haNot
    simp [edgeAt, h]
  have hnots : a ≠ L.points s := by
    intro h
    apply haNot
    simp [edgeAt, h]
  have hdist_r : dist a (L.points r) = rho := hrho _ (by simp [edgeAt])
  have hdist_s : dist a (L.points s) = rho := hrho _ (by simp [edgeAt])
  refine ⟨haA, hnotr, hnots, ?_⟩
  linarith

-- The next two CGN7c theorems depend on the missing CGN6e indexed-witness
-- bridge.  Stop here rather than inventing that geometry.

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN
