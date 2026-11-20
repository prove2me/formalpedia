-- Prove2me | solution 1 for P010.isolatedVertices_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:43:45.329094+00:00
-- url     : https://prove2.me/submissions/2c7fcd30-9c75-4764-89b1-275dff4f0bcf

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
theorem _root_.solution (n x : ℕ) (hx : x ∈ isolatedVertices n)
    (hn : 1 ≤ n) : 1 ≤ x ∧ x ≤ n := by
  rcases Finset.mem_insert.mp hx with h1 | hl
  · omega
  · obtain ⟨hp, _, hle⟩ := mem_largePrimes.mp hl
    have htwo := hp.two_le
    omega
end P010
