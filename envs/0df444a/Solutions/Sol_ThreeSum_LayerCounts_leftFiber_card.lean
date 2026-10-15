-- Prove2me | solution 1 for ThreeSum.LayerCounts.leftFiber_card
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:46:38.986999+00:00
-- url     : https://prove2.me/submissions/3ad0c0fe-d689-4d42-81f9-87f8730d9ac9

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic


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


















theorem leftFiber_card_sourceProof {L h : ℕ} (S : Finset (Fin L)) (hS : S.card = h) :
    ((edgeSet L h).filter (fun p => p.1 = S)).card = (L - h).choose h := by
  have hc : ((univ : Finset (Fin L)) \ S).card = L - h := by
    rw [card_sdiff_of_subset (subset_univ S)]
    simp [hS]
  rw [← hc, ← card_powersetCard]
  apply card_bij (fun p _ => p.2)
  · intro p hp
    rcases mem_filter.mp hp with ⟨hp, hpS⟩
    rcases mem_edgeSet.mp hp with ⟨_, hp2, hd⟩
    apply mem_powersetCard.mpr
    refine ⟨?_, hp2⟩
    intro i hi
    apply mem_sdiff.mpr
    refine ⟨mem_univ i, ?_⟩
    intro his
    exact disjoint_left.mp hd (hpS ▸ his) hi
  · intro p hp q hq he
    apply Prod.ext
    · exact (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
    · exact he
  · intro V hV
    rcases mem_powersetCard.mp hV with ⟨hsub, hcard⟩
    refine ⟨(S, V), ?_, rfl⟩
    apply mem_filter.mpr
    refine ⟨mem_edgeSet.mpr ⟨hS, hcard, ?_⟩, rfl⟩
    apply disjoint_left.mpr
    intro i his hiv
    exact (mem_sdiff.mp (hsub hiv)).2 his
































































end ThreeSum.LayerCounts

end


theorem solution : ∀ {L h : Nat} (S : Finset.{0} (Fin L)),
  @Eq.{1} Nat (@Finset.card.{0} (Fin L) S) h →
    @Eq.{1} Nat
      (@Finset.card.{0} (Prod.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)))
        ({p ∈ ThreeSum.LayerCounts.edgeSet L h |
          @Eq.{1} (Finset.{0} (Fin L)) (@Prod.fst.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)) p) S}))
      ((@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L h).choose h) := by
  exact @ThreeSum.LayerCounts.leftFiber_card_sourceProof

#print axioms solution
