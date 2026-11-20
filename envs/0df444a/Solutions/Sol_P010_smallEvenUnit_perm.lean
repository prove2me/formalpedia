-- Prove2me | solution 1 for P010.smallEvenUnit_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:49:38.353429+00:00
-- url     : https://prove2.me/submissions/0c8b0b59-c638-48cd-be29-536ebe179030

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_small_prime_even_endpoints
public import Theorems.Thm_P010_orderedPrimeClass_perm

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p : ℕ) (hp : Nat.Prime p)
    (hbound : 4 * p ≤ n) :
    (smallEvenUnit n p).Perm (primeClass n p).toList := by
  obtain ⟨hu, hv, hne⟩ := small_prime_even_endpoints n p hp hbound
  exact orderedPrimeClass_perm n p (2 * p) (4 * p) hu hv hne
end P010
