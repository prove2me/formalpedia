-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.nonempty_groupCohomology_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:54:35.48311+00:00
-- url     : https://prove2.me/submissions/76f835ff-15aa-4e65-b819-20e59c527d8f

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_Herbrand
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_nonempty_of_surjective
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_Tmap_mk
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_dHom_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_kerMap_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.Tmap_mk
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.dHom_apply
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.kerMap_coe



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
open Function CategoryTheory
universe u
variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G] {M : Type u} [AddCommGroup M] [Module k M]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
theorem _root_.solution (ρ : Representation k G M) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (hi0 : i ≠ 0) (hi : Even i) :
    Nonempty (groupCohomology (Rep.of ρ) i ≃+ TateZerothCohomology ρ g) := by
  have : NeZero i := ⟨hi0⟩
  let π := Rep.FiniteCyclicGroup.groupCohomologyπEven (Rep.of ρ) g hg i hi
  have hπ : Surjective π.hom := by
    rw [← ModuleCat.epi_iff_surjective]
    dsimp only [π, Rep.FiniteCyclicGroup.groupCohomologyπEven]
    exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)) (epi_comp' inferInstance inferInstance)
  refine nonempty_of_surjective _ (π.hom.toAddMonoidHom) hπ ?_
  intro x
  exact Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff (Rep.of ρ) g hg i hi x
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
