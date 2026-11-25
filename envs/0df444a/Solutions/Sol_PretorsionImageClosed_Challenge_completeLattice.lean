-- Prove2me | solution 1 for PretorsionImageClosed.Challenge.completeLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T07:53:55.679333+00:00
-- url     : https://prove2.me/submissions/745ae12c-d457-4fa1-b829-bca2e7eb9b1c

module
public import Definitions.Def_PretorsionImageClosed
public import Definitions.Def_PretorsionImageClosed_Solution
public import Theorems.Thm_PretorsionImageClosed_completeLattice


set_option autoImplicit true
@[expose] public section
public section
universe u
namespace PretorsionImageClosed.Challenge
theorem _root_.solution :
    PretorsionImageClosed.Statement.CompleteLattice.{u} :=
  PretorsionImageClosed.completeLattice
end PretorsionImageClosed.Challenge
