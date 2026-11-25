-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.rho_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:27:47.107858+00:00
-- url     : https://prove2.me/submissions/af0f6deb-755d-4e32-8c9a-695239682588

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalSets
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
variable (C : Subcategory (Statement.LinRep k n))
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (D : Subcategory (Statement.LinRep k 0)) : rho D.prop = 0 := by
  unfold rho
  have : IsEmpty (Skeleton (ObjectProperty.FullSubcategory (fun X : Statement.LinRep k 0 =>
      D.prop X ∧ Indecomposable X ∧ ∃ i : Fin 0, i.val + 1 = 0 ∧ ¬ IsZero (X.obj i)))) := by
    constructor
    rintro ⟨X⟩
    obtain ⟨i, -, -⟩ := X.2.2.2
    exact i.elim0
  exact Nat.card_of_isEmpty
end PretorsionImageClosed.LinearQuiver
