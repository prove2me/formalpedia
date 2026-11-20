-- Prove2me | solution 1 for P010.P010_statement_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T20:02:24.208073+00:00
-- url     : https://prove2.me/submissions/f15da158-dfac-46d2-999f-cabd4696bda0

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_P010_exact

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) : ExactStatement n := by
  intro hn
  exact P010_exact n hn
end P010
