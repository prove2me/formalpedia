-- Prove2me | solution 1 for PretorsionImageClosed.gandhiImageClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:48:20.782943+00:00
-- url     : https://prove2.me/submissions/0aa4eea0-5396-4502-9b2c-4b77dfa5dc84

module
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Definitions.Def_PretorsionImageClosed_Length_Modules
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Definitions.Def_PretorsionImageClosed_MainTheorems
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_finsum_imageClosedWeight
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_isGandhiSecond_gandhiSecondOf
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_xSum_eq
public import Theorems.Thm_PretorsionImageClosed_Statement_IsGandhiFirst_eq
public import Theorems.Thm_PretorsionImageClosed_Statement_IsGandhiSecond_eq


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
universe u
namespace PretorsionImageClosed
theorem _root_.solution : Statement.GandhiImageClosed.{u} := by
  refine ⟨⟨LinearQuiver.gandhiSecondOf, LinearQuiver.isGandhiSecond_gandhiSecondOf⟩, ?_⟩
  intro k _ n
  refine ⟨inferInstance, fun Cs hCs => ?_⟩
  rw [LinearQuiver.finsum_imageClosedWeight]
  exact (LinearQuiver.xSum_eq n).trans
    (LinearQuiver.isGandhiSecond_gandhiSecondOf.eq hCs (n + 1) (by omega))
end PretorsionImageClosed
