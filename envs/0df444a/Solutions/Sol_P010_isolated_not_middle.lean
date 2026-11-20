-- Prove2me | solution 1 for P010.isolated_not_middle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:44:23.059626+00:00
-- url     : https://prove2.me/submissions/59bd978e-9598-407f-863e-dfe39fc2d158

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_mem_largePrimes
public import Theorems.Thm_P010_mem_middlePrimes

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n x : ℕ) (hx : x ∈ isolatedVertices n) :
    x ∉ middlePrimes n := by
  intro hm
  obtain ⟨hp, _, hhalf⟩ := mem_middlePrimes.mp hm
  rcases Finset.mem_insert.mp hx with heq | hl
  · have htwo := hp.two_le
    omega
  · have hbig := (mem_largePrimes.mp hl).2.1
    omega
end P010
