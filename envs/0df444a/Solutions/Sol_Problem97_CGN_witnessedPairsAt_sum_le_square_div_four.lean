-- Prove2me | solution 1 for Problem97.CGN.witnessedPairsAt_sum_le_square_div_four
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:32.179818+00:00
-- url     : https://prove2.me/submissions/26617615-2b76-4bb8-85dd-8ab09b88f202

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN:10897:12531. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Fin
import Theorems.Thm_Problem97_CGN_card_witnessedPairsAt_le_left
import Theorems.Thm_Problem97_CGN_card_witnessedPairsAt_le_right
import Theorems.Thm_Problem97_Dumitrescu_matching_count_sum_le_square_div_four

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



































/-- CGN7a packaged as the advertised partial-matching bound at a fixed cap
vertex. -/
theorem Problem97.CGN.card_witnessedPairsAt_le_min {m : ℕ} (L : OrderedCap m) (j : Fin m)
    (hleft : ∀ {r s t : Fin m}, WitnessesCapEdgeAt L j r s →
      WitnessesCapEdgeAt L j r t → s = t)
    (hright : ∀ {r s t : Fin m}, WitnessesCapEdgeAt L j r s →
      WitnessesCapEdgeAt L j t s → r = t) :
    (WitnessedPairsAt L j).card ≤ min j.val (m - 1 - j.val) := by
  have hl := card_witnessedPairsAt_le_left L j hleft
  have hr := card_witnessedPairsAt_le_right L j hright
  exact le_min hl hr


theorem solution {m : ℕ} (L : OrderedCap m)
    (hleft : ∀ j : Fin m, ∀ {r s t : Fin m}, WitnessesCapEdgeAt L j r s →
      WitnessesCapEdgeAt L j r t → s = t)
    (hright : ∀ j : Fin m, ∀ {r s t : Fin m}, WitnessesCapEdgeAt L j r s →
      WitnessesCapEdgeAt L j t s → r = t) :
    ∑ j : Fin m, (WitnessedPairsAt L j).card ≤ (m - 1)^2 / 4 := by
  have hpoint : ∀ j : Fin m, (WitnessedPairsAt L j).card ≤
      min (j : ℕ) (m - 1 - (j : ℕ)) := by
    intro j
    have hj := card_witnessedPairsAt_le_min L j (hleft j) (hright j)
    simpa using hj
  have hsum :
      ∑ j : Fin m, (WitnessedPairsAt L j).card ≤
        ∑ j : Fin m, min (j : ℕ) (m - 1 - (j : ℕ)) := by
    simpa using (sum_le_sum (fun j _ => hpoint j))
  have hmatch :
      ∑ j : Fin m, min (j : ℕ) (m - 1 - (j : ℕ)) ≤ (m - 1)^2 / 4 := by
    have hsum_eq :
        ∑ j : Fin m, min (j : ℕ) (m - 1 - (j : ℕ)) =
          ∑ j ∈ Finset.range m, min j (m - 1 - j) := by
      simpa using
        (Fin.sum_univ_eq_sum_range (f := fun j : ℕ => min j (m - 1 - j)) m)
    calc
      ∑ j : Fin m, min (j : ℕ) (m - 1 - (j : ℕ))
          = ∑ j ∈ Finset.range m, min j (m - 1 - j) := hsum_eq
      _ ≤ (m - 1)^2 / 4 := by
        exact Problem97.Dumitrescu.matching_count_sum_le_square_div_four m
  exact hsum.trans hmatch



















-- The next two CGN7c theorems depend on the missing CGN6e indexed-witness
-- bridge.  Stop here rather than inventing that geometry.

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN
