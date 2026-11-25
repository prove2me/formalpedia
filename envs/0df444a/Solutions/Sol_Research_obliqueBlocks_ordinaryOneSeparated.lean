-- Prove2me | solution 1 for Research.obliqueBlocks_ordinaryOneSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:18:07.744955+00:00
-- url     : https://prove2.me/submissions/93b18eb2-f2f0-456e-99c2-0c952f66b12e

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_obliqueBlocks_oneSeparated

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution (m : ℕ) :
    OrdinaryOneSeparatedOn (obliqueBlocks m) := by
  intro q s hqs
  rw [Real.one_le_sqrt]
  exact obliqueBlocks_oneSeparated m q s hqs
end Research
