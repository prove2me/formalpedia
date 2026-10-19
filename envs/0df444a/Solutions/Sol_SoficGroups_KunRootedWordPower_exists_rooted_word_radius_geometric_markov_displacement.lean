-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.exists_rooted_word_radius_geometric_markov_displacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/3a85ae61-3bee-4f44-a09c-79aa7cdb611f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_kazhdanMarkovContractionFactor_lt_one
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_kazhdanMarkovContractionFactor_nonneg
import Theorems.Thm_SoficGroups_KunRootedWordPower_exists_rooted_word_radius_all_markov_iterate_contractions
import Theorems.Thm_SoficGroups_KunRootedWordPower_norm_iterate_sub_le_sum_successive
import Theorems.Thm_SoficGroups_KunRootedWordPower_sum_geometric_budget_le

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
    (k : ℕ) :
    ∃ r : ℕ, ∀ X : RootedIndicatorMarkovModel G ↥S,
      X.IsGenerated (fun i : ↥S => (i : G)) w →
      X.IsRootedAtRadius w r →
      ‖((permutationMarkov X.generator)^[k])
          (indicatorVector X.indicator) -
        indicatorVector X.indicator‖ ≤
      (2 / (1 - kazhdanMarkovContractionFactor P S)) *
        ‖permutationMarkov X.generator
            (indicatorVector X.indicator) -
          indicatorVector X.indicator‖ := by
  let q := kazhdanMarkovContractionFactor P S
  have hqzero : 0 ≤ q :=
    kazhdanMarkovContractionFactor_nonneg P S
  have hqone : q < 1 :=
    kazhdanMarkovContractionFactor_lt_one P S ⟨1, honeS⟩
  let ε : ℝ := (((k + 1 : ℕ) : ℝ) * (1 - q))⁻¹
  have hε : 0 < ε :=
    inv_pos.mpr (mul_pos (by positivity) (sub_pos.mpr hqone))
  obtain ⟨r, hr⟩ :=
    exists_rooted_word_radius_all_markov_iterate_contractions
      P S honeS hcover hsymmetric w k ε hε
  refine ⟨r, ?_⟩
  intro X hgenerated hroot
  let d : ℝ :=
    ‖permutationMarkov X.generator
        (indicatorVector X.indicator) -
      indicatorVector X.indicator‖
  have hsteps : ∀ j ∈ Finset.range k,
      ‖((permutationMarkov X.generator)^[j + 1])
          (indicatorVector X.indicator) -
        ((permutationMarkov X.generator)^[j])
          (indicatorVector X.indicator)‖ ≤
        (q ^ j + ε) * d := by
    intro j hj
    exact hr X hgenerated hroot j
      (Nat.le_of_lt (Finset.mem_range.mp hj))
  calc
    ‖((permutationMarkov X.generator)^[k])
        (indicatorVector X.indicator) -
      indicatorVector X.indicator‖ ≤
        ∑ j ∈ Finset.range k,
          ‖((permutationMarkov X.generator)^[j + 1])
              (indicatorVector X.indicator) -
            ((permutationMarkov X.generator)^[j])
              (indicatorVector X.indicator)‖ :=
      norm_iterate_sub_le_sum_successive
        (permutationMarkov X.generator)
        (indicatorVector X.indicator) k
    _ ≤ ∑ j ∈ Finset.range k, (q ^ j + ε) * d :=
      Finset.sum_le_sum hsteps
    _ = (∑ j ∈ Finset.range k, (q ^ j + ε)) * d := by
      rw [Finset.sum_mul]
    _ ≤ (2 / (1 - q)) * d :=
      mul_le_mul_of_nonneg_right
        (sum_geometric_budget_le q hqzero hqone k)
        (norm_nonneg _)
    _ = (2 / (1 - kazhdanMarkovContractionFactor P S)) *
        ‖permutationMarkov X.generator
            (indicatorVector X.indicator) -
          indicatorVector X.indicator‖ := by
      rfl
end SoficGroups.KunRootedWordPower
