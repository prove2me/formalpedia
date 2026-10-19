-- Prove2me | solution 1 for SoficGroups.CompletedSelectedCentralizerPairwiseSource.eventually_five_mul_sourceCompletionBad_le_of_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/df62671e-7bdc-4b98-ace0-15516dd4b2b9

import Mathlib
import Definitions.Def_NonSoficGroup

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
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    {ι J : Type*} [Fintype ι] [Group J]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (p : (n : ℕ) → J → Equiv.Perm (V n))
    (F : Finset J)
    (Z : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Z n).Nonempty)
    (hbad : Tendsto
      (fun n =>
        ((sourceCompletionBad
          (σ n) (p n) F (Z n)).card : ℝ) / (Z n).card)
      atTop (nhds 0)) :
    ∀ᶠ n in atTop,
      5 * (sourceCompletionBad
        (σ n) (p n) F (Z n)).card ≤ (Z n).card := by
  have hsmall : ∀ᶠ n in atTop,
      ((sourceCompletionBad
        (σ n) (p n) F (Z n)).card : ℝ) /
          (Z n).card < (1 / 5 : ℝ) :=
    hbad.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hsmall] with n hn
  have hpositive : (0 : ℝ) < (Z n).card := by
    exact_mod_cast (hZ n).card_pos
  have hreal := (div_lt_iff₀ hpositive).mp hn
  have hstrict :
      5 * (sourceCompletionBad
        (σ n) (p n) F (Z n)).card < (Z n).card := by
    exact_mod_cast (show
      (5 : ℝ) * (sourceCompletionBad
        (σ n) (p n) F (Z n)).card < (Z n).card by
          linarith)
  exact hstrict.le
end SoficGroups.CompletedSelectedCentralizerPairwiseSource
