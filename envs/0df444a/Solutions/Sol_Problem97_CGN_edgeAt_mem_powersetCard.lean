-- Prove2me | solution 1 for Problem97.CGN.edgeAt_mem_powersetCard
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:05:43.475983+00:00
-- url     : https://prove2.me/submissions/cdc4ccd3-1925-433e-8016-12679ab9c44d

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN:13097:13742. -/
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














































theorem solution {m : ℕ} {A : Finset ℝ²} (L : OrderedCap m)
    (hmem : ∀ t : Fin m, L.points t ∈ A) {r s : Fin m} (hrs : r < s) :
    edgeAt L r s ∈ A.powersetCard 2 := by
  rw [Finset.mem_powersetCard]
  refine ⟨?_, ?_⟩
  · intro x hx
    simp [edgeAt] at hx
    rcases hx with rfl | rfl
    · exact hmem r
    · exact hmem s
  · have hne : L.points r ≠ L.points s := by
      intro h
      exact (ne_of_lt hrs) (L.injective h)
    simpa [edgeAt] using (Finset.card_pair hne)











-- The next two CGN7c theorems depend on the missing CGN6e indexed-witness
-- bridge.  Stop here rather than inventing that geometry.

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN
