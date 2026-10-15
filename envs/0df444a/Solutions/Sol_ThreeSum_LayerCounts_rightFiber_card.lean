-- Prove2me | solution 1 for ThreeSum.LayerCounts.rightFiber_card
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:18:21.38967+00:00
-- url     : https://prove2.me/submissions/7c20eba9-e228-44fe-9ee4-853acfc74c58

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Theorems.Thm_ThreeSum_LayerCounts_leftFiber_card


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Exact counts for the local subset graph

These are counts of the executable finite sets used by the graph, rather
than abstract numerical cardinality hypotheses.  An edge is an ordered
pair of disjoint `h`-subsets of `Fin L`.
-/

namespace ThreeSum.LayerCounts

open Finset
















































theorem rightFiber_card_sourceProof {L h : ℕ} (V : Finset (Fin L)) (hV : V.card = h) :
    ((edgeSet L h).filter (fun p => p.2 = V)).card = (L - h).choose h := by
  rw [← leftFiber_card V hV]
  apply card_bij (fun p _ => p.swap)
  · intro p hp
    rcases mem_filter.mp hp with ⟨hp, hpV⟩
    rcases mem_edgeSet.mp hp with ⟨h1, h2, hd⟩
    exact mem_filter.mpr ⟨mem_edgeSet.mpr ⟨h2, h1, hd.symm⟩, hpV⟩
  · intro p hp q hq he
    exact Prod.swap_injective he
  · intro p hp
    rcases mem_filter.mp hp with ⟨hp, hpV⟩
    rcases mem_edgeSet.mp hp with ⟨h1, h2, hd⟩
    exact ⟨p.swap, mem_filter.mpr ⟨mem_edgeSet.mpr ⟨h2, h1, hd.symm⟩, hpV⟩,
      Prod.swap_swap p⟩
















































end ThreeSum.LayerCounts

end


theorem solution : ∀ {L h : Nat} (V : Finset.{0} (Fin L)),
  @Eq.{1} Nat (@Finset.card.{0} (Fin L) V) h →
    @Eq.{1} Nat
      (@Finset.card.{0} (Prod.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)))
        ({p ∈ ThreeSum.LayerCounts.edgeSet L h |
          @Eq.{1} (Finset.{0} (Fin L)) (@Prod.snd.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)) p) V}))
      ((@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L h).choose h) := by
  exact @ThreeSum.LayerCounts.rightFiber_card_sourceProof

#print axioms solution
