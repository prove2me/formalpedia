-- Prove2me | solution 1 for PretorsionImageClosed.Statement.psiTerm_insert_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:20:50.5648+00:00
-- url     : https://prove2.me/submissions/3e515589-7a2d-4b85-82a2-8383d0488d50

module
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial Finset
variable {ι : Type*} [LinearOrder ι]
namespace PretorsionImageClosed.Statement
theorem _root_.solution {r : ι} {R Cont : Finset ι} (hr : ∀ x ∈ R, x < r)
    (hCont : Cont ⊆ R) : psiTerm (insert r R) Cont = psiTerm R Cont := by
  unfold psiTerm
  congr 3
  apply Finset.filter_congr
  intro e he
  constructor
  · intro h a ha hae
    exact h a (Finset.mem_insert_of_mem ha) hae
  · intro h a ha hae
    rcases Finset.mem_insert.1 ha with rfl | ha'
    · exact absurd hae (not_lt.2 (hr e (hCont he)).le)
    · exact h a ha' hae
end PretorsionImageClosed.Statement
