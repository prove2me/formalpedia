-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_h1_equiv_characters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:11:16.209516+00:00
-- url     : https://prove2.me/submissions/17c6ed89-b42c-48cc-878f-875f01f52000

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_one_coboundaries_trivial_eq_bot
import Theorems.Thm_ReciprocityTheory_Coh_low_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution : ∃ e : (trivRep G QZ).H 1 ≃+ charGrp G,
    ∀ x hx g, (e ((trivRep G QZ).coch.cls 1 x hx)).1 (Additive.ofMul g) = x.1 ![g] := by
  obtain ⟨-, -, ⟨e, he⟩, -⟩ := low_holds ℤ G (trivRep G QZ)
  have hB : (Gal.B1 (trivRep G QZ).rho).comap (Gal.Z1 (trivRep G QZ).rho).subtype = ⊥ := by
    rw [one_coboundaries_trivial_eq_bot, Submodule.comap_bot, Submodule.ker_subtype]
  refine ⟨e.toAddEquiv.trans ((Submodule.quotEquivOfEqBot _ hB).toAddEquiv.trans (oneCocycleEquivCharacters G)), ?_⟩
  intro x hx g
  obtain ⟨hz, h⟩ := he x hx
  show (oneCocycleEquivCharacters G (Submodule.quotEquivOfEqBot _ hB (e _))).1 (Additive.ofMul g) = _
  rw [h, Submodule.quotEquivOfEqBot_apply_mk]
  rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
