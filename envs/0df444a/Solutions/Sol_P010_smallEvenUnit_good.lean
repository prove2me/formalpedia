-- Prove2me | solution 1 for P010.smallEvenUnit_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:49:42.759851+00:00
-- url     : https://prove2.me/submissions/49c97ccc-50a2-4660-af09-3ea7a82d5095

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_small_prime_even_endpoints
public import Theorems.Thm_P010_orderedPrimeClass_chain
public import Theorems.Thm_P010_orderedPrimeClass_head
public import Theorems.Thm_P010_orderedPrimeClass_last

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p : ℕ) (hp : Nat.Prime p)
    (hbound : 4 * p ≤ n) :
    NonCoprimeChain (smallEvenUnit n p) ∧
      EvenEnded (smallEvenUnit n p) := by
  obtain ⟨hu, hv, _⟩ := small_prime_even_endpoints n p hp hbound
  have hc : NonCoprimeChain (smallEvenUnit n p) :=
    orderedPrimeClass_chain n p (2 * p) (4 * p) hp hu hv
  refine ⟨hc, 2 * p, 4 * p, ?_, ?_, ?_, ?_⟩
  · exact orderedPrimeClass_head n p (2 * p) (4 * p)
  · exact orderedPrimeClass_last n p (2 * p) (4 * p)
  · exact ⟨p, by omega⟩
  · exact ⟨2 * p, by omega⟩
end P010
