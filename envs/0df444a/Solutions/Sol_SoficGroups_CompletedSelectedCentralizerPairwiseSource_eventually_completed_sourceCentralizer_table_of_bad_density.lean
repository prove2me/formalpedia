-- Prove2me | solution 1 for SoficGroups.CompletedSelectedCentralizerPairwiseSource.eventually_completed_sourceCentralizer_table_of_bad_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/69c9d886-4ab1-4085-9ade-54e29d58e624

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_completedRestriction_mul_distance_le_sourceCompletionBad
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_completedRestriction_separated_of_sourceCompletionBad
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_completedRestriction_commutationDefect_le_sourceCompletionBad
import Theorems.Thm_SoficGroups_CompletedSelectedCentralizerPairwiseSource_eventually_five_mul_sourceCompletionBad_le_of_density

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedSelectedCentralizerPairwiseSource
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedFirstStageWordRadiusTransfer
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open scoped BigOperators Pointwise
namespace SoficGroups.CompletedSelectedCentralizerPairwiseSource
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    {ι J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (Z : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Z n).Nonempty)
    (hbad : Tendsto
      (fun n =>
        ((sourceCompletionBad
          (σ n) (p n) F (Z n)).card : ℝ) /
            (Z n).card)
      atTop (nhds 0))
    (σZ : (n : ℕ) → ι →
      Equiv.Perm {x : V n // x ∈ Z n})
    (hσZ : ∀ n i (x : V n) (hx : x ∈ Z n)
      (_hi : σ n i x ∈ Z n),
        ((σZ n i ⟨x, hx⟩ :
          {x : V n // x ∈ Z n}) : V n) = σ n i x)
    (t : ℕ → ℕ)
    (ht : ∀ n,
      2 * Fintype.card ι *
        (sourceCompletionBad
          (σ n) (p n) F (Z n)).card ≤ t n) :
    ∀ᶠ n in atTop,
      (∀ a ∈ F, ∀ b ∈ F,
        5 * SoficGroups.permutationDistance
          (completedRestriction (p n (a * b)) (Z n))
          (completedRestriction (p n a) (Z n) *
            completedRestriction (p n b) (Z n)) ≤
          Fintype.card {x : V n // x ∈ Z n}) ∧
      (∀ a ∈ F, ∀ b ∈ F, a ≠ b →
        Fintype.card {x : V n // x ∈ Z n} <
          5 * SoficGroups.permutationDistance
            (completedRestriction (p n a) (Z n))
            (completedRestriction (p n b) (Z n))) ∧
      (∀ a ∈ SoficGroups.CompressionCriterion.productTrackedTable F,
        SoficGroups.permutationCommutationDefect
          (σZ n) (completedRestriction (p n a) (Z n)) ≤
            t n) := by
  have hevent :=
    eventually_five_mul_sourceCompletionBad_le_of_density
      V σ p F Z hZ hbad
  filter_upwards [hevent] with n hn
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    have hdist :=
      completedRestriction_mul_distance_le_sourceCompletionBad
        (σ n) (p n) F (Z n) ha hb
    simpa only [Fintype.card_coe] using
      (Nat.mul_le_mul_left 5 hdist).trans hn
  · intro a ha b hb hab
    exact completedRestriction_separated_of_sourceCompletionBad
      (σ n) (p n) F (Z n) (hZ n) hn ha hb hab
  · intro a ha
    have hdef :=
      completedRestriction_commutationDefect_le_sourceCompletionBad
        (σ n) (p n) F (Z n)
        (σZ n) (hσZ n) ha
    have hscale :
        Fintype.card ι *
          (sourceCompletionBad
            (σ n) (p n) F (Z n)).card ≤ t n := by
      have hdegree : Fintype.card ι ≤ 2 * Fintype.card ι := by
        omega
      exact (Nat.mul_le_mul_right
        (sourceCompletionBad
          (σ n) (p n) F (Z n)).card hdegree).trans (ht n)
    exact hdef.trans hscale
end SoficGroups.CompletedSelectedCentralizerPairwiseSource
