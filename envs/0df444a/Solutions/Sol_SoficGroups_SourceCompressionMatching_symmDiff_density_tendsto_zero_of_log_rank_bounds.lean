-- Prove2me | solution 1 for SoficGroups.SourceCompressionMatching.symmDiff_density_tendsto_zero_of_log_rank_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/067ca1e7-d2a1-425a-9c8b-6a48fbe20108

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matchedRetainedSupport_subset
import Theorems.Thm_SoficGroups_matchedRetainedSupport_card

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionMatching
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.SourceCompressionMatching
theorem _root_.solution
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (D : ∀ n, Finset (V n) → Finset (V n))
    (H eta : ℕ → ℝ)
    (hH : ∀ n, 0 ≤ H n) (heta : ∀ n, 0 ≤ eta n)
    (hHzero : Tendsto H atTop (nhds 0))
    (hetazero : Tendsto eta atTop (nhds 0))
    (hbound : ∀ n C, C ∈ R n →
      ((C ∆ D n C).card : ℝ) ≤
        (Real.exp (H n) - 1 + 2 * eta n) * (C.card : ℝ)) :
    Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card)
      atTop (nhds 0) := by
  have hcoeff : Tendsto
      (fun n => Real.exp (H n) - 1 + 2 * eta n)
      atTop (nhds 0) := by
    have hexp : Tendsto (fun n => Real.exp (H n)) atTop (nhds 1) := by
      simpa [Function.comp_def] using
        (Real.continuous_exp.tendsto (0 : ℝ)).comp hHzero
    have hfirst : Tendsto
        (fun n => Real.exp (H n) - 1) atTop (nhds 0) := by
      simpa using hexp.sub_const 1
    have hsecond : Tendsto
        (fun n => (2 : ℝ) * eta n) atTop (nhds 0) := by
      simpa using hetazero.const_mul 2
    simpa only [zero_add] using hfirst.add hsecond
  refine squeeze_zero (fun n => by positivity) ?_ hcoeff
  intro n
  have hpos : (0 : ℝ) < (U n).card := by
    exact_mod_cast (hU n).card_pos
  have hexp : 1 ≤ Real.exp (H n) := by
    simpa using (Real.exp_le_exp.mpr (hH n))
  have hnonneg : 0 ≤ Real.exp (H n) - 1 + 2 * eta n := by
    nlinarith [heta n]
  have hmassnat :
      (∑ C ∈ R n, C.card) ≤ (U n).card := by
    calc
      (∑ C ∈ R n, C.card) =
          (SoficGroups.matchedRetainedSupport (R n)).card :=
        (SoficGroups.matchedRetainedSupport_card
          (P n) (R n) (hR n)).symm
      _ ≤ (U n).card :=
        Finset.card_le_card
          (SoficGroups.matchedRetainedSupport_subset
            (P n) (R n) (hR n))
  have hmass :
      (∑ C ∈ R n, (C.card : ℝ)) ≤ (U n).card := by
    exact_mod_cast hmassnat
  have hsum :
      ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) ≤
        (Real.exp (H n) - 1 + 2 * eta n) *
          (∑ C ∈ R n, (C.card : ℝ)) := by
    calc
      ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) =
          ∑ C ∈ R n, ((C ∆ D n C).card : ℝ) := by
            simp
      _ ≤ ∑ C ∈ R n,
          (Real.exp (H n) - 1 + 2 * eta n) * (C.card : ℝ) := by
            exact Finset.sum_le_sum fun C hC => hbound n C hC
      _ = (Real.exp (H n) - 1 + 2 * eta n) *
          (∑ C ∈ R n, (C.card : ℝ)) := by
            rw [Finset.mul_sum]
  calc
    ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card ≤
        ((Real.exp (H n) - 1 + 2 * eta n) *
          (∑ C ∈ R n, (C.card : ℝ))) / (U n).card :=
      (div_le_div_iff_of_pos_right hpos).2 hsum
    _ ≤ ((Real.exp (H n) - 1 + 2 * eta n) *
          (U n).card) / (U n).card := by
      apply (div_le_div_iff_of_pos_right hpos).2
      exact mul_le_mul_of_nonneg_left hmass hnonneg
    _ = Real.exp (H n) - 1 + 2 * eta n := by
      field_simp
end SoficGroups.SourceCompressionMatching
