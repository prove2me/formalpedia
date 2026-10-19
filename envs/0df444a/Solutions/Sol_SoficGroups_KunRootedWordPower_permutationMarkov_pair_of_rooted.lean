-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.permutationMarkov_pair_of_rooted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/959015f8-f5d7-44d9-9c99-11d15290f6c7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_normalizedPairDisplacement_diagonal

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {G ι V : Type*} [Group G] [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (s : ι → G)
    (hgenerator : ∀ i, σ (s i) = p i)
    (q : G × G)
    (hroot : ∀ i,
      (∀ x : V, indicatorVector f x ≠ 0 →
        σ (s i * q.1) x = (σ (s i) * σ q.1) x) ∧
      (∀ x : V, indicatorVector f x ≠ 0 →
        σ (s i * q.2) x = (σ (s i) * σ q.2) x)) :
    permutationMarkov p (normalizedPairDisplacement p f σ q) =
      pairedWordAverage s (normalizedPairDisplacement p f σ) 1 q := by
  simp only [permutationMarkov, pairedWordAverage]
  apply congrArg (fun x => (Fintype.card ι : ℂ)⁻¹ • x)
  apply Finset.sum_congr rfl
  intro i _
  rw [← hgenerator i]
  exact (normalizedPairDisplacement_diagonal p f σ
    (s i) q.1 q.2 (hroot i).1 (hroot i).2).symm
end SoficGroups.KunRootedWordPower
