-- Prove2me | solution 1 for ThreeSum.LayerCounts.unionFiber_card
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:46:39.618251+00:00
-- url     : https://prove2.me/submissions/c9b33a5f-6c5a-402b-9a20-ac810e18e90c

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
































































theorem unionFiber_card_sourceProof {L h : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = 2 * h) :
    ((edgeSet L h).filter (fun p => p.1 ∪ p.2 = Q)).card = (2 * h).choose h := by
  rw [← hQ, ← card_powersetCard]
  apply card_bij (fun p _ => p.1)
  · intro p hp
    rcases mem_filter.mp hp with ⟨hp, hpQ⟩
    exact mem_powersetCard.mpr ⟨hpQ ▸ subset_union_left, (mem_edgeSet.mp hp).1⟩
  · intro p hp q hq he
    rcases mem_filter.mp hp with ⟨hp, hpQ⟩
    rcases mem_filter.mp hq with ⟨hq, hqQ⟩
    have hpV : Q \ p.1 = p.2 := by
      rw [← hpQ]
      exact union_sdiff_cancel_left (mem_edgeSet.mp hp).2.2
    have hqV : Q \ q.1 = q.2 := by
      rw [← hqQ]
      exact union_sdiff_cancel_left (mem_edgeSet.mp hq).2.2
    exact Prod.ext he (by rw [← hpV, ← hqV, he])
  · intro S hS
    rcases mem_powersetCard.mp hS with ⟨hsub, hcard⟩
    refine ⟨(S, Q \ S), ?_, rfl⟩
    apply mem_filter.mpr
    refine ⟨mem_edgeSet.mpr ⟨hcard, ?_, ?_⟩, union_sdiff_of_subset hsub⟩
    · rw [card_sdiff_of_subset hsub, hQ, hcard]
      omega
    · exact disjoint_sdiff_self_right






















end ThreeSum.LayerCounts

end


theorem solution : ∀ {L h : Nat} (Q : Finset.{0} (Fin L)),
  @Eq.{1} Nat (@Finset.card.{0} (Fin L) Q)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h) →
    @Eq.{1} Nat
      (@Finset.card.{0} (Prod.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)))
        ({p ∈ ThreeSum.LayerCounts.edgeSet L h |
          @Eq.{1} (Finset.{0} (Fin L))
            (@Union.union.{0} (Finset.{0} (Fin L)) (@Finset.instUnion.{0} (Fin L) (instDecidableEqFin L))
              (@Prod.fst.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)) p)
              (@Prod.snd.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L)) p))
            Q}))
      ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h).choose
        h) := by
  exact @ThreeSum.LayerCounts.unionFiber_card_sourceProof

#print axioms solution
