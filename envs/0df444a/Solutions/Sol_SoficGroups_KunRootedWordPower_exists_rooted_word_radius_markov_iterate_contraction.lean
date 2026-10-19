-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.exists_rooted_word_radius_markov_iterate_contraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/0ed61d7b-e87f-466d-beda-dcdaf84b6429

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedWordPower_exists_rooted_word_radius_normalized_markov_contraction
import Theorems.Thm_SoficGroups_KunRootedWordPower_permutationMarkov_iterate_difference
import Theorems.Thm_SoficGroups_KunRootedWordPower_norm_normalizedIndicatorDefect_markov_pow

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
      ‖((permutationMarkov X.generator)^[k + 1])
            (indicatorVector X.indicator) -
          ((permutationMarkov X.generator)^[k])
            (indicatorVector X.indicator)‖ ≤
        (kazhdanMarkovContractionFactor P S ^ k + ε) *
          ‖permutationMarkov X.generator
              (indicatorVector X.indicator) -
            indicatorVector X.indicator‖ := by
  obtain ⟨r, hr⟩ :=
    exists_rooted_word_radius_normalized_markov_contraction
      P S honeS hcover hsymmetric w k ε hε
  refine ⟨r, ?_⟩
  intro X hgenerated hroot
  by_cases hfixed :
      permutationMarkov X.generator
        (indicatorVector X.indicator) =
          indicatorVector X.indicator
  · rw [Function.iterate_fixed hfixed (k + 1),
      Function.iterate_fixed hfixed k, hfixed]
    simp
  · have hpositive :
        0 < ‖permutationMarkov X.generator
          (indicatorVector X.indicator) -
            indicatorVector X.indicator‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hfixed)
    have hnormalized := hr X hgenerated hroot hfixed
    rw [norm_normalizedIndicatorDefect_markov_pow]
      at hnormalized
    have hdenormalized :=
      (div_lt_iff₀ hpositive).mp hnormalized
    rw [permutationMarkov_iterate_difference]
    exact hdenormalized.le
end SoficGroups.KunRootedWordPower
