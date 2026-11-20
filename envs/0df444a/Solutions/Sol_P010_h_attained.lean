-- Prove2me | solution 1 for P010.h_attained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:42:34.37919+00:00
-- url     : https://prove2.me/submissions/4ddef728-9eda-4beb-86c4-cbbfe9ab8141

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) : Attained n (h n) := by
  classical
  exact Nat.find_spec (attainable n)
end P010
