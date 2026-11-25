-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.multiplicative_cochain_h1_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:11:15.887868+00:00
-- url     : https://prove2.me/submissions/8a1ea6b9-7092-4435-8cba-dc0c0f82c085

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiveTerm
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KbarRepContAction
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_kbar_cocycle
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_memZ
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_mem_oneCoboundaries_iff
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_mk_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_wach_d1_eq_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution : Subsingleton ((kbarT p K).H 1) := by
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ x : (kbarT p K).H 1, x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mk_eq_zero_iff, mem_oneCoboundaries_iff]
    have hz : (kbarT p K).coch.d 1 z.1 = 0 := (memZ z.1).1 z.2
    exact kbar_cocycle p K (fun h => z.1.1 (e1 h))
      (Continuous.comp z.1.2 (continuous_pi fun _ => continuous_id))
      ((wach_d1_eq_zero_iff _ z.1).1 hz)
  rw [h0 x, h0 y]
end ReciprocityTheory.DiscreteGroups.LocalClassField
