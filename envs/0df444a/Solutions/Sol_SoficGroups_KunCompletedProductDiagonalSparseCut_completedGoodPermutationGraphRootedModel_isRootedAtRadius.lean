-- Prove2me | solution 1 for SoficGroups.KunCompletedProductDiagonalSparseCut.completedGoodPermutationGraphRootedModel_isRootedAtRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/cbf5a0eb-eb53-4dc7-ab6a-78200a500bf2

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
    {G ι V : Type u} [Group G]
    [Fintype V] [DecidableEq V]
    (w : G → List ι) (σ : ι → Equiv.Perm V)
    (φ : G → Equiv.Perm V)
    (p : Equiv.Perm V) (B : Finset V) (r : ℕ)
    (hroot : ∀ a g : G,
      (w a).length + (w g).length + (w (a * g)).length ≤ r →
        ∀ x : V, x ∉ B →
          φ (a * g) x = (φ a * φ g) x) :
    (completedGoodPermutationGraphRootedModel
      σ φ p B).IsRootedAtRadius w r := by
  refine ⟨?_⟩
  intro a g hword z hz
  have hzreal :
      completedGoodPermutationGraphIndicator
        (goodPermutationGraph p B) z ≠ 0 := by
    intro hzero
    apply hz
    change
      (completedGoodPermutationGraphIndicator
        (goodPermutationGraph p B) z : ℂ) = 0
    exact_mod_cast hzero
  have hzgraph : z ∈ goodPermutationGraph p B := by
    by_contra hnot
    apply hzreal
    exact if_neg hnot
  have hgood : z.1 ∉ B ∧ z.2 ∉ B :=
    (Finset.mem_filter.mp hzgraph).2
  apply Prod.ext
  · exact hroot a g hword z.1 hgood.1
  · exact hroot a g hword z.2 hgood.2
end SoficGroups.KunCompletedProductDiagonalSparseCut
