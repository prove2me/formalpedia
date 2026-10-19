-- Prove2me | solution 1 for SoficGroups.matched_eventually_exists_good_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/45074c7a-f3dc-416b-9da2-e2d10806ce18

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    (C B : ∀ n, Finset (V n)) (hC : ∀ n, (C n).Nonempty)
    (hbad : Tendsto
      (fun n => (((C n ∩ B n).card : ℝ) / (C n).card))
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∃ x ∈ C n, x ∉ B n := by
  filter_upwards [hbad.eventually (gt_mem_nhds zero_lt_one)] with n hn
  by_contra h
  push Not at h
  have heq : C n ∩ B n = C n := Finset.inter_eq_left.2 h
  have hc : ((C n).card : ℝ) ≠ 0 := by
    exact_mod_cast (hC n).card_pos.ne'
  rw [heq, div_self hc] at hn
  exact (lt_irrefl (1 : ℝ)) hn
end SoficGroups
