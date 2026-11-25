-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.pert_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:05:16.4541+00:00
-- url     : https://prove2.me/submissions/70b0673b-7120-49e4-b81b-6d1f9c14788e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA

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
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution (E : Finset ℂ) (c : ℂ) (ε δ : ℝ) :
    ContinuousOn (pert E c ε δ) (↑E)ᶜ := by
  have hlog : ∀ f ∈ E, ContinuousOn (fun ζ : ℂ => log ‖ζ - f‖) (↑E)ᶜ := by
    intro f hf
    apply ContinuousOn.log (by fun_prop)
    intro x hx hx0
    rw [norm_eq_zero, sub_eq_zero] at hx0
    exact hx (hx0 ▸ hf)
  unfold pert
  exact (continuousOn_const.mul (continuousOn_finsetSum E hlog)).add (by fun_prop)
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
