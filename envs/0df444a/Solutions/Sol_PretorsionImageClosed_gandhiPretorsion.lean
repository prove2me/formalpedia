-- Prove2me | solution 1 for PretorsionImageClosed.gandhiPretorsion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:28:29.765797+00:00
-- url     : https://prove2.me/submissions/7cfae6a6-9fcc-45dc-b646-6309ad9d6eae

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Definitions.Def_PretorsionImageClosed_MainTheorems
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_cpSum_eq
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_finsum_pretorsionWeight
public import Theorems.Thm_PretorsionImageClosed_Statement_isGandhiFirst_gandhiFirst


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
universe u
namespace PretorsionImageClosed
theorem _root_.solution : Statement.GandhiPretorsion.{u} := by
  refine ⟨⟨gandhiFirst, isGandhiFirst_gandhiFirst⟩, ?_⟩
  intro k _ n
  refine ⟨inferInstance, fun B hB => ?_⟩
  rw [LinearQuiver.finsum_pretorsionWeight]
  exact LinearQuiver.cpSum_eq hB n
end PretorsionImageClosed
