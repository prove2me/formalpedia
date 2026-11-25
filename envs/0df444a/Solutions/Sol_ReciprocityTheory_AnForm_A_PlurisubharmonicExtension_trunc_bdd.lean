-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.trunc_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:51.579035+00:00
-- url     : https://prove2.me/submissions/60af5ff5-c3dd-4f4f-96a4-7546ea4c491b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_local_bound


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
theorem _root_.solution {z : Fin D → ℂ} (hz : z ∈ U) :
    IsBoundedUnder (· ≤ ·) (𝓝[U \ coordDiv S] z) (trunc u κ) := by
  obtain ⟨ρ, hρ, M, hM⟩ := local_bound hU hU1 hc hpsh hg hz
  refine isBoundedUnder_of_eventually_le (a := max M (-κ)) ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z hρ), self_mem_nhdsWithin]
    with y hy hyV
  exact max_le_max (hM y ⟨hy, hyV.2⟩) le_rfl
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
