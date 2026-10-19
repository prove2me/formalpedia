-- Prove2me | solution 1 for SoficGroups.MatchedComponentExitBudget.pruned_component_card_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/7adeca9c-37b4-454d-854f-10866cd0f086

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentExitBudget
open Filter Topology
open scoped BigOperators
namespace SoficGroups.MatchedComponentExitBudget
theorem _root_.solution
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (B : (n : ℕ) → Finset (V n))
    (hsize : Tendsto (fun n => Fintype.card (V n)) atTop atTop)
    (hdeleted : Tendsto
      (fun n => ((B n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto (fun n => (Finset.univ \ B n : Finset (V n)).card)
      atTop atTop := by
  have hhalf : ∀ᶠ n in atTop,
      ((B n).card : ℝ) / Fintype.card (V n) < (1 / 2 : ℝ) :=
    hdeleted.eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hpositive : ∀ᶠ n in atTop, 0 < Fintype.card (V n) := by
    have hevent := (Filter.tendsto_atTop.1 hsize) 1
    filter_upwards [hevent] with n hn
    omega
  have hhalfsize :
      Tendsto (fun n => Fintype.card (V n) / 2) atTop atTop :=
    (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hsize
  refine tendsto_atTop_mono' atTop ?_ hhalfsize
  filter_upwards [hhalf, hpositive] with n hn hnpositive
  have hrealpos : (0 : ℝ) < Fintype.card (V n) := by
    exact_mod_cast hnpositive
  have hratio := (div_lt_iff₀ hrealpos).1 hn
  have hbadlt : 2 * (B n).card < Fintype.card (V n) := by
    exact_mod_cast (show
      (2 : ℝ) * (B n).card < Fintype.card (V n) by linarith)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ (B n)),
    Finset.card_univ]
  omega
end SoficGroups.MatchedComponentExitBudget
