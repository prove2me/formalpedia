-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Norm.holoSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:24:49.10932+00:00
-- url     : https://prove2.me/submissions/04d082a5-a059-4576-89be-bf8f5e822c4c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_HoloSectionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_Section

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Norm
open Filter Topology Asymptotics
universe u
namespace ReciprocityTheory.L2DbarEstimates.Norm
theorem _root_.solution : holoSectionStatement.{u} := by
  intro n M _ z f hz hf s w hs hzs
  obtain ⟨e, hxe, rfl⟩ := hz (s w)
  have hchart : IsChart n e e := fun _ _ => rfl
  have hw : e (s w) = w := hzs.self_of_nhds
  have htarget : e.target ∈ 𝓝 w := by
    rw [← hw]
    exact e.open_target.mem_nhds (e.map_source hxe)
  have hsrc : ∀ᶠ v in 𝓝 w, s v ∈ e.source := hs (e.open_source.mem_nhds hxe)
  have heq : f ∘ e.symm =ᶠ[𝓝 w] f ∘ s := by
    filter_upwards [hsrc, hzs] with v h1 h2
    simp only [Function.comp_apply]
    rw [show e.symm v = s v by rw [← e.left_inv h1, h2]]
  exact ((hf e hchart).differentiableAt htarget).congr_of_eventuallyEq heq.symm
end ReciprocityTheory.L2DbarEstimates.Norm
