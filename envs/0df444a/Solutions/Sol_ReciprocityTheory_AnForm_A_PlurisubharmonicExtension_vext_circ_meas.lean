-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.vext_circ_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:05:14.310718+00:00
-- url     : https://prove2.me/submissions/3375cab4-22a7-4541-8257-ab1f848eb71a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_vext_usc

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
theorem _root_.solution {P : ℝ → Fin D → ℂ} (hP : Continuous P) (hPU : ∀ θ, P θ ∈ U) :
    Measurable (fun θ => vext U S u κ (P θ)) :=
  (upperSemicontinuousOn_univ_iff.1 ((vext_usc hU hU1 hc hpsh hg).comp hP.continuousOn
    (fun θ _ => hPU θ))).measurable
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
