-- Prove2me | solution 1 for Research.shellSixBlockIncidence_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:13:11.970866+00:00
-- url     : https://prove2.me/submissions/9714dca6-8b1b-42d4-a863-7b4e9d81a47e

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_shellSixIncidence_card

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution (m : ℕ) :
    Fintype.card (ShellSixBlockIncidence m) = m * 16786618 := by
  rw [Fintype.card_prod, Fintype.card_fin, shellSixIncidence_card]
end Research
