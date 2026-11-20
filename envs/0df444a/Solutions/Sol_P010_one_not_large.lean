-- Prove2me | solution 1 for P010.one_not_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:43:40.243851+00:00
-- url     : https://prove2.me/submissions/6f478817-0d90-4e73-a596-01e0f12c42aa

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
theorem _root_.solution (n : ℕ) : 1 ∉ largePrimes n := by
  intro h
  have hp := (mem_largePrimes.mp h).1
  have htwo := hp.two_le
  omega
end P010
