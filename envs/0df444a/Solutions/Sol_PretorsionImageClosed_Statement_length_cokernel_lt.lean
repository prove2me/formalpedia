-- Prove2me | solution 1 for PretorsionImageClosed.Statement.length_cokernel_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:52:22.121956+00:00
-- url     : https://prove2.me/submissions/1cb870de-73d1-48ed-a401-c9c696df6eff

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Theorems.Thm_PretorsionImageClosed_length_lt_of_epi


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
namespace PretorsionImageClosed.Statement
theorem _root_.solution {X : C} {S : Subobject X} (hS : S ≠ ⊥) :
    length (cokernel S.arrow) < length X := by
  apply length_lt_of_epi (cokernel.π S.arrow)
  intro hiso
  apply hS
  rw [← Subobject.mk_arrow S, Subobject.mk_eq_bot_iff_zero, ← cancel_mono (cokernel.π S.arrow),
    cokernel.condition, zero_comp]
end PretorsionImageClosed.Statement
