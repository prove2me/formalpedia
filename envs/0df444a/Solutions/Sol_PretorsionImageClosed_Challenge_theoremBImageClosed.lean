-- Prove2me | solution 1 for PretorsionImageClosed.Challenge.theoremBImageClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:10:05.686417+00:00
-- url     : https://prove2.me/submissions/42720b32-42b2-4c1f-82f9-762666bb09ea

module
public import Definitions.Def_PretorsionImageClosed
public import Definitions.Def_PretorsionImageClosed_Solution
public import Theorems.Thm_PretorsionImageClosed_theoremBImageClosed


set_option autoImplicit true
@[expose] public section
public section
universe u
namespace PretorsionImageClosed.Challenge
theorem _root_.solution :
    PretorsionImageClosed.Statement.TheoremBImageClosed.{u} :=
  PretorsionImageClosed.theoremBImageClosed
end PretorsionImageClosed.Challenge
