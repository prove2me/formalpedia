-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.vext_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:47.869423+00:00
-- url     : https://prove2.me/submissions/022aaff2-b175-4373-957b-08139735cdd6

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_nebot_diff
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_vext_of_not
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_vext_of_mem
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_trunc_bdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
open ReciprocityTheory.AnForm.A
variable {D : ℕ} {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C κ : ℝ}
variable (hU : IsOpen U) (hU1 : U ⊆ ball 0 1) (hc : ContinuousOn u (U \ coordDiv S))
    (hpsh : IsPsh (U \ coordDiv S) u)
    (hg : ∀ z ∈ U \ coordDiv S, u z ≤ C * log (exp 1 + ∑ i ∈ S, log ‖z i‖⁻¹))
include hU hU1 hc hpsh hg
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution {z : Fin D → ℂ} (hz : z ∈ U) : -κ ≤ vext U S u κ z := by
  by_cases hA : z ∈ coordDiv S
  · rw [vext_of_mem hA]
    have := nebot_diff (S := S) hU hz
    refine le_limsup_of_le (trunc_bdd hU hU1 hc hpsh hg hz) (fun b hb => ?_)
    obtain ⟨y, hy⟩ := hb.exists
    exact (le_max_right (u y) (-κ)).trans hy
  · rw [vext_of_not hA]; exact le_max_right _ _
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
