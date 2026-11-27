-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_isChain_fullChain_49524c90c477
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:29.703831+00:00
-- url     : https://prove2.me/submissions/96b7af7a-46f5-4140-b3c7-bbc2289dcd37

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Parabolic
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_orth_antitone_7a7d283f0c36
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_le_orth_of_mem_4c827d4221dd
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Module Matrix TensorProduct GroundTheory.Automorphic NumberField
open scoped NumberField.AdeleRing
noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical
variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K) (H : Matrix ι ι E)
variable {K H}
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (𝒲 : IsotropicFlag K H) :
    IsChain (· ≤ ·) (fullChain 𝒲 : Set (Submodule E (ι → E))) := by
  have key : ∀ A ∈ fullChain 𝒲, ∀ B ∈ fullChain 𝒲, A ≤ B ∨ B ≤ A := by
    intro A hA B hB
    simp only [fullChain, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hA hB
    rcases hA with rfl | rfl | hA | ⟨W, hW, rfl⟩
    · exact Or.inl bot_le
    · exact Or.inr le_top
    · rcases hB with rfl | rfl | hB | ⟨W', hW', rfl⟩
      · exact Or.inr bot_le
      · exact Or.inl le_top
      · rcases eq_or_ne A B with rfl | hne
        · exact Or.inl le_rfl
        · exact 𝒲.isChain hA hB hne
      · exact Or.inl (le_orth_of_mem 𝒲 hA hW')
    · rcases hB with rfl | rfl | hB | ⟨W', hW', rfl⟩
      · exact Or.inr bot_le
      · exact Or.inl le_top
      · exact Or.inr (le_orth_of_mem 𝒲 hB hW)
      · rcases eq_or_ne W W' with rfl | hne
        · exact Or.inl le_rfl
        · rcases 𝒲.isChain hW hW' hne with h | h
          · exact Or.inr (orth_antitone h)
          · exact Or.inl (orth_antitone h)
  intro A hA B hB _
  exact key A hA B hB
end GroundTheory.Heights₂.Theta
