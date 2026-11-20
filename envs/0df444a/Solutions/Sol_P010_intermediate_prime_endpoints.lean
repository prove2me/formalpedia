-- Prove2me | solution 1 for P010.intermediate_prime_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:34:27.456757+00:00
-- url     : https://prove2.me/submissions/8ffe4d53-fd7e-460e-9310-83f9670796b7

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_two_mul_prime_mem_class
public import Theorems.Thm_P010_three_mul_prime_mem_class

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p : ℕ) (hn : 12 ≤ n)
    (hp : Nat.Prime p) (hquarter : n / 4 < p)
    (hthird : p ≤ n / 3) :
    2 * p ∈ primeClass n p ∧
      3 * p ∈ primeClass n p ∧ 2 * p ≠ 3 * p := by
  have hp3 : 3 ≤ p := by omega
  constructor
  · exact two_mul_prime_mem_class n p hp (by omega)
  constructor
  · exact three_mul_prime_mem_class n p hp hp3 (by omega)
  · have := hp.two_le
    omega
end P010
