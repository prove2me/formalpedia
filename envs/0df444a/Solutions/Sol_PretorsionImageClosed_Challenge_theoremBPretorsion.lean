-- Prove2me | solution 1 for PretorsionImageClosed.Challenge.theoremBPretorsion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:43:47.247793+00:00
-- url     : https://prove2.me/submissions/a9f2a922-c0b5-496b-b4bb-603104e9f9b7

module
public import Definitions.Def_PretorsionImageClosed
public import Definitions.Def_PretorsionImageClosed_Solution
public import Theorems.Thm_PretorsionImageClosed_theoremBPretorsion


set_option autoImplicit true
@[expose] public section
public section
universe u
namespace PretorsionImageClosed.Challenge
theorem _root_.solution :
    PretorsionImageClosed.Statement.TheoremBPretorsion.{u} :=
  PretorsionImageClosed.theoremBPretorsion
end PretorsionImageClosed.Challenge
