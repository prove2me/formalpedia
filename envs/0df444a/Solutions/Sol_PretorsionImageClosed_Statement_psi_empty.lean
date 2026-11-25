-- Prove2me | solution 1 for PretorsionImageClosed.Statement.psi_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:20:29.554397+00:00
-- url     : https://prove2.me/submissions/b451bd55-4f2d-4da8-a0e6-3039d0c754c9

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
theorem _root_.solution : psi (∅ : Finset ι) = 1 := by
  simp [psi, psiTerm]
end PretorsionImageClosed.Statement
