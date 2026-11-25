-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_h2_int_equiv_characters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:06:28.988803+00:00
-- url     : https://prove2.me/submissions/a9829ce7-9485-428e-add1-4e7c053eaf2c

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_admissible_int_rat_sequence
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_conn_int_rat_bijective
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_h1_equiv_characters
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
theorem _root_.solution [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    ∃ e : (trivRep G ℤ).H 2 ≃+ charGrp G, ∀ δ, Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ →
      ∀ x hx g, (e (δ 1 ((trivRep G QZ).coch.cls 1 x hx))).1 (Additive.ofMul g) = x.1 ![g] := by
  have hs := admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)
  obtain ⟨⟨δ', h1, -⟩, hu⟩ := lES_holds ℤ _ _ _ _ _ hs
  obtain ⟨e, he⟩ := exists_h1_equiv_characters G
  let d : (trivRep G QZ).H 1 ≃+ (trivRep G ℤ).H 2 :=
    AddEquiv.ofBijective (δ' 1).toAddMonoidHom (conn_int_rat_bijective G δ' h1 1 one_pos)
  refine ⟨d.symm.trans e, fun δ hδ x hx g => ?_⟩
  obtain rfl := hu δ δ' hδ h1
  show (e (d.symm (d _))).1 _ = _
  rw [d.symm_apply_apply, he]
end ReciprocityTheory.DiscreteGroups.LocalClassField
