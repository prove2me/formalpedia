-- Prove2me | solution 1 for SoficGroups.RankArcCharging.rankChangingArc_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/e7df0112-8fe5-45cf-8e29-08c61ed04e9a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_RankArcCharging_rankChangingArc_card_le_crossing_add_unselected

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.RankArcCharging
open scoped BigOperators
namespace SoficGroups.RankArcCharging
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n))
    (P : ∀ n, Finpartition (U n))
    (b : ∀ n, V n → ℤ)
    (j : ∀ n, Finset (V n) → ℤ)
    (w : ∀ n, Equiv.Perm (V n))
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (hcross : Filter.Tendsto
      (fun n => ((partitionWordCrossing (P n) (w n)).card : ℝ) / N n)
      Filter.atTop (nhds 0))
    (homit : Filter.Tendsto
      (fun n =>
        (((U n \ selectedRankSupport (P n) (b n) (j n)).card : ℝ) /
          N n))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ((rankChangingArc (U n) (b n) (w n)).card : ℝ) / N n)
      Filter.atTop (nhds 0) := by
  have hnonnegative : ∀ n,
      0 ≤ ((rankChangingArc (U n) (b n) (w n)).card : ℝ) / N n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (hN n).le
  have hupper : ∀ n,
      ((rankChangingArc (U n) (b n) (w n)).card : ℝ) / N n ≤
        ((partitionWordCrossing (P n) (w n)).card : ℝ) / N n +
          2 * (((U n \ selectedRankSupport (P n) (b n) (j n)).card : ℝ) /
            N n) := by
    intro n
    have hnat := rankChangingArc_card_le_crossing_add_unselected
      (P n) (b n) (j n) (w n)
    have hreal :
        ((rankChangingArc (U n) (b n) (w n)).card : ℝ) ≤
          ((partitionWordCrossing (P n) (w n)).card : ℝ) +
            2 * ((U n \ selectedRankSupport (P n) (b n) (j n)).card : ℝ) := by
      exact_mod_cast hnat
    calc
      ((rankChangingArc (U n) (b n) (w n)).card : ℝ) / N n ≤
          (((partitionWordCrossing (P n) (w n)).card : ℝ) +
            2 * ((U n \ selectedRankSupport (P n) (b n) (j n)).card : ℝ)) /
              N n :=
        div_le_div_of_nonneg_right hreal (hN n).le
      _ = ((partitionWordCrossing (P n) (w n)).card : ℝ) / N n +
          2 * (((U n \ selectedRankSupport (P n) (b n) (j n)).card : ℝ) /
            N n) := by
        ring
  have hlimit : Filter.Tendsto
      (fun n =>
        ((partitionWordCrossing (P n) (w n)).card : ℝ) / N n +
          2 * (((U n \ selectedRankSupport (P n) (b n) (j n)).card : ℝ) /
            N n))
      Filter.atTop (nhds 0) := by
    simpa using hcross.add (Filter.Tendsto.const_mul (2 : ℝ) homit)
  exact squeeze_zero'
    (Filter.Eventually.of_forall hnonnegative)
    (Filter.Eventually.of_forall hupper)
    hlimit
end SoficGroups.RankArcCharging
