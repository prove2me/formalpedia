-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.IsTorsion.le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:54:23.391096+00:00
-- url     : https://prove2.me/submissions/1f002a7a-189f-4f85-ab89-42803982709e

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TorsionPairs
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_isTorsion_iff_middle
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_prop_iff_prop_trace


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
theorem _root_.solution {P Q : PretorsionTheory C} (hP : P.IsTorsion) (hQ : Q.IsTorsion) :
    P ≤ Q ↔ P.T ≤ Q.T := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun Y hY => ?_⟩⟩
  have hQm := (isTorsion_iff_middle Q).1 hQ
  have hPm := (isTorsion_iff_middle P).1 hP
  have hz : IsZero (Q.T.trace Y : C) := by
    have := (Q.isPretorsionTheory.prop_iff_prop_trace Y).1 hY
    have h' : Q.middle (Q.T.trace Y : C) := this
    rw [hQm] at h'
    exact h'
  have hle : P.T.trace Y ≤ Q.T.trace Y :=
    le_trace Q.isPretorsionTheory.isQuotientClosed (h _ (P.T.prop_trace Y))
  have hz' : IsZero (P.T.trace Y : C) := IsZero.of_mono (Subobject.ofLE _ _ hle) hz
  exact (P.isPretorsionTheory.prop_iff_prop_trace Y).2
    ⟨P.T.prop_of_isZero hz', P.F.prop_of_isZero hz'⟩
end IsTorsion
end PretorsionImageClosed.Statement.PretorsionTheory
