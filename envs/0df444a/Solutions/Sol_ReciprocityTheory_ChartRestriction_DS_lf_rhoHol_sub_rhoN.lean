-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lf_rhoHol_sub_rhoN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:26:29.579881+00:00
-- url     : https://prove2.me/submissions/282227c6-cd32-45a9-8d4c-788e53ddcf24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_cfa_rho_coord


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
theorem _root_.solution (ε : Fin n → Bool) (c : Fin n) :
    (rhoHol ε - rhoN ε) c = if ε c = true then ((univ.filter fun a => ε a = false ∧ a < c).card : ℝ)
      else -((univ.filter fun i => ε i = true ∧ c < i).card : ℝ) := by
  rw [cfa_rho_coord]
  cases hc : ε c <;> simp [hc, Finset.sum_boole]
end ReciprocityTheory.ChartRestriction.DS
