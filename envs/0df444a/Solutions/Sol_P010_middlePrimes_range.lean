-- Prove2me | solution 1 for P010.middlePrimes_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:44:22.439341+00:00
-- url     : https://prove2.me/submissions/fe479de8-6927-4683-955e-9a410ae08f7a

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_mem_middlePrimes

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n x : ℕ) (hx : x ∈ middlePrimes n) :
    1 ≤ x ∧ x ≤ n := by
  obtain ⟨hp, _, hle⟩ := mem_middlePrimes.mp hx
  have htwo := hp.two_le
  omega
end P010
