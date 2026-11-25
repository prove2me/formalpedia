-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.IsTorsion.eq_of_T_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:55:32.068806+00:00
-- url     : https://prove2.me/submissions/5b1a40d4-b9c3-4ce1-9e47-3d7e09286fb0

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TorsionPairs
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_IsTorsion_le_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_le_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_iff


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory ZeroObject
variable {C : Type*} [Category C] [Abelian C]
variable [HasLength C]
open PretorsionImageClosed.Statement.PretorsionTheory
namespace PretorsionImageClosed.Statement.PretorsionTheory
namespace IsTorsion
theorem _root_.solution {P Q : PretorsionTheory C} (hP : P.IsTorsion) (hQ : Q.IsTorsion)
    (h : P.T = Q.T) : P = Q :=
  le_antisymm ((hP.le_iff hQ).2 h.le) ((hQ.le_iff hP).2 h.ge)
end IsTorsion
end PretorsionImageClosed.Statement.PretorsionTheory
