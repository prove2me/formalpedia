-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:24.880495+00:00
-- url     : https://prove2.me/submissions/9cf4b7cc-e0e8-4a7d-bab4-2b943149b5d7

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt

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
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution (hU : IsOpen U) {z : Fin D → ℂ} (hz : z ∈ U) :
    (𝓝[U \ coordDiv S] z).NeBot := by
  have hT : Tendsto (fun t : ℝ => z + (t : ℂ) • (fun _ => (1 : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have : Continuous (fun t : ℝ => z + (t : ℂ) • (fun _ => (1 : ℂ))) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), z + (t : ℂ) • (fun _ => (1 : ℂ)) ∈ U \ coordDiv S := by
    have h1 := hT.eventually (hU.mem_nhds hz)
    have h2 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ i ∈ S, z i + (t : ℂ) ≠ 0 := by
      rw [eventually_all_finset]
      intro i _
      by_cases hzi : z i = 0
      · filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hzi, zero_add]
        exact_mod_cast (ne_of_gt ht)
      · have hc : Tendsto (fun t : ℝ => z i + (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (z i)) := by
          have : Continuous (fun t : ℝ => z i + (t : ℂ)) := by fun_prop
          simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
        exact hc.eventually_ne hzi
    filter_upwards [h1, h2] with t ht1 ht2
    refine ⟨ht1, ?_⟩
    rintro ⟨i, hi, h0⟩
    apply ht2 i hi
    simpa using h0
  exact (tendsto_nhdsWithin_iff.2 ⟨hT, hev⟩).neBot
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
