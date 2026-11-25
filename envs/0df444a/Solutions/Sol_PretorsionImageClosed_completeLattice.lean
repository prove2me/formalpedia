-- Prove2me | solution 1 for PretorsionImageClosed.completeLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:50:43.611801+00:00
-- url     : https://prove2.me/submissions/a509a60a-39c0-4743-a1dd-8f6107ecab8f

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Definitions.Def_PretorsionImageClosed_MainTheorems
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_bot_eq
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sInf_F_prop
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sInf_T_prop
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sSup_F_prop
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_sSup_T_prop
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_top_eq
public import Theorems.Thm_PretorsionImageClosed_isArtinianRing_mop


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
universe u
namespace PretorsionImageClosed
theorem _root_.solution : Statement.CompleteLattice.{u} := by
  intro k _ Λ _ _ _
  haveI := isNoetherianRing_mop k Λ
  haveI := isArtinianRing_mop k Λ
  refine ⟨inferInstance, fun P Q => Iff.rfl, fun S _ => ⟨PretorsionTheory.sInf_T_prop S,
    PretorsionTheory.sInf_F_prop S⟩, fun S _ => ⟨PretorsionTheory.sSup_T_prop S,
    PretorsionTheory.sSup_F_prop S⟩, ?_, ?_, ?_, ?_⟩
  · rw [PretorsionTheory.bot_eq]
    rfl
  · rw [PretorsionTheory.bot_eq]
    rfl
  · rw [PretorsionTheory.top_eq]
    rfl
  · rw [PretorsionTheory.top_eq]
    rfl
end PretorsionImageClosed
