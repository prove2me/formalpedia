-- Prove2me | solution 1 for SoficGroups.matchedRetainedSupport_cover_density_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/8016695c-c43a-4fc3-8ab6-371ed8790e43

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matchedRetainedSupport_subset

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (hdiscard : Tendsto
      (fun n => (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
        (U n).card)) atTop (𝓝 0)) :
    Tendsto
      (fun n => ((matchedRetainedSupport (R n)).card : ℝ) / (U n).card)
      atTop (𝓝 1) := by
  have hform (n : ℕ) :
      ((matchedRetainedSupport (R n)).card : ℝ) / (U n).card =
        1 - (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card) := by
    have hcard := Finset.card_sdiff_add_card_eq_card
      (matchedRetainedSupport_subset (P n) (R n) (hR n))
    have hreal :
        ((U n \ matchedRetainedSupport (R n)).card : ℝ) +
          (matchedRetainedSupport (R n)).card = (U n).card := by
      exact_mod_cast hcard
    have hden : ((U n).card : ℝ) ≠ 0 := by
      exact_mod_cast (hU n).card_pos.ne'
    field_simp
    linarith
  have hlimit : Tendsto
      (fun n =>
        (1 : ℝ) - (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card)) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hdiscard :
        Tendsto
          (fun n =>
            (1 : ℝ) - (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
              (U n).card))
          atTop (𝓝 ((1 : ℝ) - 0)))
  convert hlimit using 1
  funext n
  exact hform n
end SoficGroups
