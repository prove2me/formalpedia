-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.vext_usc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:57:51.971193+00:00
-- url     : https://prove2.me/submissions/cd360442-31df-4e1d-ac88-d0da771ea8e6

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_coordDiv_closed
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_vext_of_not
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_vext_of_mem
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_trunc_bdd
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_trunc_cobdd

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
theorem _root_.solution : UpperSemicontinuousOn (vext U S u κ) U := by
  have hVo : IsOpen (U \ coordDiv S) := hU.sdiff (coordDiv_closed S)
  intro z hz b hb
  by_cases hA : z ∈ coordDiv S
  · rw [vext_of_mem hA] at hb
    obtain ⟨c, hc1, hc2⟩ := exists_between hb
    have h1 := eventually_lt_of_limsup_lt hc1 (trunc_bdd hU hU1 hc hpsh hg hz)
    rw [eventually_nhdsWithin_iff] at h1
    have h2 := h1.eventually_nhds
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds h2, self_mem_nhdsWithin] with y hy hyU
    by_cases hyA : y ∈ coordDiv S
    · rw [vext_of_mem hyA]
      refine lt_of_le_of_lt (limsup_le_of_le (trunc_cobdd hU hU1 hc hpsh hg hyU) ?_) hc2
      rw [eventually_nhdsWithin_iff]
      exact hy.mono fun y' hy' hy'V => (hy' hy'V).le
    · rw [vext_of_not hyA]
      exact lt_trans (hy.self_of_nhds ⟨hyU, hyA⟩) hc2
  · rw [vext_of_not hA] at hb
    have hcz : ContinuousAt (fun x => max (u x) (-κ)) z :=
      (hc.sup continuousOn_const).continuousAt (hVo.mem_nhds ⟨hz, hA⟩)
    have h1 := hcz.eventually (gt_mem_nhds hb)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds h1,
      mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds ⟨hz, hA⟩)] with y hy hyV
    rw [vext_of_not hyV.2]
    exact hy
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
