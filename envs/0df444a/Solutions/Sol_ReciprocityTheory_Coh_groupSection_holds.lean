-- Prove2me | solution 1 for ReciprocityTheory.Coh.groupSection_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:32:50.339422+00:00
-- url     : https://prove2.me/submissions/c5848b24-7a5e-4bb1-9582-8f551074786e

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_SectionA
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Theorems.Thm_ReciprocityTheory_Coh_ContinuousSections_core


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Function
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : GroupSectionStatement.{u} := by
  intro G _ _ _ _ _ _ U hU
  obtain ⟨t, ht, htU, hc⟩ := ContinuousSections.core U hU
  let r0 : G → U := fun g => ⟨g * (t g)⁻¹, by simpa using U.inv_mem (htU g)⟩
  have hr0 : Continuous r0 := (continuous_id.mul ht.inv).subtype_mk _
  refine ⟨fun g => r0 g * (r0 1)⁻¹, hr0.mul continuous_const, mul_inv_cancel _, ?_⟩
  intro x g
  have h : t (x * g) = t g := hc _ _ (by rw [mul_inv_cancel_right]; exact x.2)
  apply Subtype.ext
  simp only [r0, Subgroup.coe_mul, Subgroup.coe_inv, h, mul_assoc]
end ReciprocityTheory.Coh
