-- Prove2me | solution 1 for PretorsionImageClosed.theoremA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:48:31.058217+00:00
-- url     : https://prove2.me/submissions/cd348d23-0f70-45bf-a4ef-91ae3f2bff3e

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Definitions.Def_PretorsionImageClosed_MainTheorems
public import Theorems.Thm_PretorsionImageClosed_Statement_isImageClosed_iff_exists_pretorsionTheory
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
theorem _root_.solution : Statement.TheoremA.{u} := by
  intro k _ Λ _ _ _
  haveI := isNoetherianRing_mop k Λ
  haveI := isArtinianRing_mop k Λ
  intro Z
  exact ⟨isImageClosed_iff_eq_gen_inf_cogen Z, isImageClosed_iff_exists_pretorsionTheory Z⟩
end PretorsionImageClosed
