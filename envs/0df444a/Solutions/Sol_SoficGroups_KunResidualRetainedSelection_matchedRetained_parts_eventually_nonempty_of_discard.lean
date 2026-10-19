-- Prove2me | solution 1 for SoficGroups.KunResidualRetainedSelection.matchedRetained_parts_eventually_nonempty_of_discard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/c0664e4e-48bc-4949-b251-a744876ff828

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualRetainedSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff
namespace SoficGroups.KunResidualRetainedSelection
theorem _root_.solution
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (R : ∀ n, Finset (Finset (V n)))
    (hdiscard : Tendsto
      (fun n =>
        (((U n \ SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, (R n).Nonempty := by
  filter_upwards [hdiscard.eventually (gt_mem_nhds zero_lt_one)] with n hn
  by_contra hR
  have hrempty : R n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
  have hucard : ((U n).card : ℝ) ≠ 0 := by
    exact_mod_cast (hU n).card_pos.ne'
  have hsupport : SoficGroups.matchedRetainedSupport (R n) = ∅ := by
    simp [SoficGroups.matchedRetainedSupport, hrempty]
  simp only [hsupport, Finset.sdiff_empty] at hn
  rw [div_self hucard] at hn
  exact (lt_irrefl (1 : ℝ)) hn
end SoficGroups.KunResidualRetainedSelection
