-- Prove2me | solution 1 for P010.two_not_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:44:32.768824+00:00
-- url     : https://prove2.me/submissions/728ca552-85ec-4460-aa2c-29486edb008a

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_mem_largePrimes

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (hn : 4 ≤ n) :
    2 ∉ isolatedVertices n := by
  intro hx
  rcases Finset.mem_insert.mp hx with h1 | hl
  · omega
  · have hbig := (mem_largePrimes.mp hl).2.1
    omega
end P010
