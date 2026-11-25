-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.wd_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:42:44.913801+00:00
-- url     : https://prove2.me/submissions/ced4c320-e2eb-47b6-b10e-1b9a092d64dc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wd_ind
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wd_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (μ : Fin n → ℝ) :
    ∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b), (μ a - μ b) = 2 * dot μ (rhoC ε - rhoN ε) := by
  have h1 : ∀ a, ∑ b ∈ univ.filter (fun b => wdP ε a b), (μ a - μ b) =
      ∑ b, (if wdP ε a b then μ a else 0) - ∑ b, (if wdP ε a b then μ b else 0) := by
    intro a; rw [sum_filter, ← sum_sub_distrib]
    exact sum_congr rfl (fun b _ => by split_ifs <;> simp)
  have h2 : ∑ a, ∑ b, (if wdP ε a b then μ b else 0) = ∑ a, ∑ b, (if wdP ε b a then μ a else 0) :=
    Finset.sum_comm
  rw [sum_congr rfl (fun a _ => h1 a), sum_sub_distrib, h2, ← sum_sub_distrib, dot, mul_sum]
  refine sum_congr rfl (fun a _ => ?_)
  rw [← sum_sub_distrib]
  have hk : ∀ b, (if wdP ε a b then μ a else 0) - (if wdP ε b a then μ a else 0) =
      μ a * ((if wdP ε a b then (1:ℝ) else 0) - (if wdP ε b a then (1:ℝ) else 0)) := by
    intro b; split_ifs <;> ring
  simp only [hk, wd_ind, ← mul_sum, sum_sub_distrib, Pi.sub_apply, rhoC, rhoN, wd_card]
  ring
end ReciprocityTheory.ChartRestriction.DS
