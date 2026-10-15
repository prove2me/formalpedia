-- Prove2me | solution 1 for ThreeSum.LayerCounts.edgeSet_card
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:18:20.724823+00:00
-- url     : https://prove2.me/submissions/2e6b4d25-d261-499a-a78d-adac4005765c

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











theorem vertices_card (L h : ℕ) : (vertices L h).card = L.choose h := by
  simp [vertices, card_powersetCard]













































































theorem vertex_degree_identity (L h : ℕ) :
    L.choose h * (L - h).choose h = L.choose (2 * h) * (2 * h).choose h := by
  simpa [show 2 * h - h = h by omega] using
    (Nat.choose_mul (n := L) (k := 2 * h) (s := h) (by omega)).symm

theorem edgeSet_card_sourceProof (L h : ℕ) :
    (edgeSet L h).card = L.choose (2 * h) * (2 * h).choose h := by
  calc
    (edgeSet L h).card =
        ∑ S ∈ vertices L h, ((edgeSet L h).filter (fun p => p.1 = S)).card := by
      apply card_eq_sum_card_fiberwise
      intro p hp
      exact mem_vertices.mpr (mem_edgeSet.mp hp).1
    _ = ∑ S ∈ vertices L h, (L - h).choose h := by
      apply sum_congr rfl
      intro S hS
      exact leftFiber_card S (mem_vertices.mp hS)
    _ = L.choose h * (L - h).choose h := by
      simp [vertices_card]
    _ = _ := vertex_degree_identity L h

end ThreeSum.LayerCounts

end


theorem solution : ∀ (L h : Nat),
  @Eq.{1} Nat
    (@Finset.card.{0} (Prod.{0, 0} (Finset.{0} (Fin L)) (Finset.{0} (Fin L))) (ThreeSum.LayerCounts.edgeSet L h))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (L.choose
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h))
      ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h).choose
        h)) := by
  exact @ThreeSum.LayerCounts.edgeSet_card_sourceProof

#print axioms solution
