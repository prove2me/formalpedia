-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.trivial_inflation_h2_int_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:56:31.582937+00:00
-- url     : https://prove2.me/submissions/06af7f41-dff4-4375-be6e-7eff1e729e30

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_BrUnrA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_trivial_inflation_h1_rat_mod_int_injective
import Theorems.Thm_ReciprocityTheory_Coh_admissibility_holds
import Theorems.Thm_ReciprocityTheory_Coh_connNat_holds
import Theorems.Thm_ReciprocityTheory_Coh_lES_holds
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_admissible_int_rat_sequence
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_conn_int_rat_bijective


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
variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G']
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [CompactSpace G']
    [T2Space G'] [TotallyDisconnectedSpace G'] (φ : G' →* G) (hφ : Continuous φ) (hs : Surjective φ) :
    Injective ((trivInfl φ hφ ℤ).hom.H 2) := by
  have s := admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)
  have s' := admissibility_holds ℤ G' _ _ _ _ _ (admissible_int_rat_sequence G')
  obtain ⟨⟨δ, h1, -⟩, -⟩ := lES_holds ℤ _ _ _ _ _ s
  obtain ⟨⟨δ', h1', -⟩, -⟩ := lES_holds ℤ _ _ _ _ _ s'
  have hnat := connNat_holds ℤ _ _ _ _ _ _ _ _ _ _ (trivInfl φ hφ ℤ).hom (trivInfl φ hφ ℚ).hom
    (trivInfl φ hφ QZ).hom δ δ' s s' (fun _ _ => rfl) (fun _ _ => rfl) h1 h1' 1
  intro a b hab
  obtain ⟨a', rfl⟩ := (conn_int_rat_bijective G δ h1 1 one_pos).2 a
  obtain ⟨b', rfl⟩ := (conn_int_rat_bijective G δ h1 1 one_pos).2 b
  have hab' : δ' 1 ((trivInfl φ hφ QZ).hom.H 1 a') = δ' 1 ((trivInfl φ hφ QZ).hom.H 1 b') :=
    (hnat a').trans (hab.trans (hnat b').symm)
  rw [trivial_inflation_h1_rat_mod_int_injective φ hφ hs ((conn_int_rat_bijective G' δ' h1' 1 one_pos).1 hab')]
end ReciprocityTheory.DiscreteGroups.LocalClassField
