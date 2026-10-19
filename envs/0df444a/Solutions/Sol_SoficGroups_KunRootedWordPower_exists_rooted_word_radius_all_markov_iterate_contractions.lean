-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.exists_rooted_word_radius_all_markov_iterate_contractions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/db9c43fa-7d58-4275-93d8-efbf6ff4b422

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedWordPower_exists_rooted_word_radius_markov_iterate_contraction
import Theorems.Thm_SoficGroups_KunRootedWordPower_RootedIndicatorMarkovModel_IsRootedAtRadius_mono

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {G : Type u} [Group G]
    (P : SoficGroups.KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, ∀ X : RootedIndicatorMarkovModel G ↥S,
      X.IsGenerated (fun i : ↥S => (i : G)) w →
      X.IsRootedAtRadius w r →
      ∀ j ≤ k,
        ‖((permutationMarkov X.generator)^[j + 1])
              (indicatorVector X.indicator) -
            ((permutationMarkov X.generator)^[j])
              (indicatorVector X.indicator)‖ ≤
          (kazhdanMarkovContractionFactor P S ^ j + ε) *
            ‖permutationMarkov X.generator
                (indicatorVector X.indicator) -
              indicatorVector X.indicator‖ := by
  classical
  have hexists : ∀ j : ℕ, ∃ r : ℕ,
      ∀ X : RootedIndicatorMarkovModel G ↥S,
        X.IsGenerated (fun i : ↥S => (i : G)) w →
        X.IsRootedAtRadius w r →
        ‖((permutationMarkov X.generator)^[j + 1])
              (indicatorVector X.indicator) -
            ((permutationMarkov X.generator)^[j])
              (indicatorVector X.indicator)‖ ≤
          (kazhdanMarkovContractionFactor P S ^ j + ε) *
            ‖permutationMarkov X.generator
                (indicatorVector X.indicator) -
              indicatorVector X.indicator‖ :=
    fun j => exists_rooted_word_radius_markov_iterate_contraction
      P S honeS hcover hsymmetric w j ε hε
  choose r hr using hexists
  let R := ∑ j ∈ Finset.range (k + 1), r j
  refine ⟨R, ?_⟩
  intro X hgenerated hroot j hj
  have hjmem : j ∈ Finset.range (k + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)
  have hrj : r j ≤ R := by
    exact Finset.single_le_sum
      (f := r) (fun i _ => Nat.zero_le _) hjmem
  exact hr j X hgenerated (hroot.mono hrj)
end SoficGroups.KunRootedWordPower
