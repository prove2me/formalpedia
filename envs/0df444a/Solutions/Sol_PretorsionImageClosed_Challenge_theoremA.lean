-- Prove2me | solution 1 for PretorsionImageClosed.Challenge.theoremA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:53:46.336929+00:00
-- url     : https://prove2.me/submissions/b9728ad8-f8e3-4aad-8a2f-d7c4d0d89349

module
public import Definitions.Def_PretorsionImageClosed
public import Definitions.Def_PretorsionImageClosed_Solution
public import Theorems.Thm_PretorsionImageClosed_theoremA


set_option autoImplicit true
@[expose] public section
public section
universe u
namespace PretorsionImageClosed.Challenge
theorem _root_.solution : PretorsionImageClosed.Statement.TheoremA.{u} :=
  PretorsionImageClosed.theoremA
end PretorsionImageClosed.Challenge
