-- Prove2me | solution 1 for SoficGroups.KunCompletedProductDiagonalSparseCut.completedGoodPermutationGraphRootedModel_isGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/113453c4-7002-4061-acdd-8e2b5629cf4b

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedProductDiagonalSparseCut
open SoficGroups.KunDiagonalGoodRootGraphLoss
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff
universe u
namespace SoficGroups.KunCompletedProductDiagonalSparseCut
theorem _root_.solution
    {G ι V : Type u} [Group G] [Fintype ι]
    [Fintype V] [DecidableEq V]
    (s : ι → G) (w : G → List ι)
    (σ : ι → Equiv.Perm V) (φ : G → Equiv.Perm V)
    (hword : ∀ g : G, φ g = ((w g).map σ).prod)
    (hone : φ 1 = 1)
    (hgenerator : ∀ i : ι, φ (s i) = σ i)
    (p : Equiv.Perm V) (B : Finset V) :
    (completedGoodPermutationGraphRootedModel σ φ p B).IsGenerated s w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    change
      completedGoodPermutationGraphIndicator
          (goodPermutationGraph p B) z = 0 ∨
        completedGoodPermutationGraphIndicator
          (goodPermutationGraph p B) z = 1
    unfold completedGoodPermutationGraphIndicator
    by_cases hz : z ∈ goodPermutationGraph p B
    · exact Or.inr (if_pos hz)
    · exact Or.inl (if_neg hz)
  · intro g
    change
      completedDiagonalPermutationHom (φ g) =
        ((w g).map
          fun i : ι => completedDiagonalPermutationHom (σ i)).prod
    rw [hword g, map_list_prod, List.map_map]
    rfl
  · change
      completedDiagonalPermutationHom (φ 1) =
        (1 : Equiv.Perm (V × V))
    rw [hone, map_one]
  · intro i
    change
      completedDiagonalPermutationHom (φ (s i)) =
        completedDiagonalPermutationHom (σ i)
    rw [hgenerator i]
end SoficGroups.KunCompletedProductDiagonalSparseCut
