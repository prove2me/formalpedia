-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.conn_int_rat_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:31:17.77943+00:00
-- url     : https://prove2.me/submissions/1675dd70-b51f-4230-8036-e5cf086b0e1b

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_h_rat_subsingleton
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_admissible_int_rat_sequence
import Theorems.Thm_ReciprocityTheory_Coh_admissibility_holds
import Theorems.Thm_ReciprocityTheory_Coh_lES_holds


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
theorem _root_.solution [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (δ : ∀ n, (trivRep G QZ).H n →ₗ[ℤ] (trivRep G ℤ).H (n + 1))
    (hδ : Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ) (n : ℕ) (hn : 0 < n) :
    Bijective (δ n) := by
  have hs := admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)
  obtain ⟨⟨δ', h1, h2⟩, hu⟩ := lES_holds ℤ _ _ _ _ _ hs
  obtain rfl := hu δ δ' hδ h1
  have s1 := h_rat_subsingleton G n hn
  have s2 := h_rat_subsingleton G (n + 1) n.succ_pos
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (h2.exC n x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    exact (h2.exA n y).1 (Subsingleton.elim _ _)
end ReciprocityTheory.DiscreteGroups.LocalClassField
