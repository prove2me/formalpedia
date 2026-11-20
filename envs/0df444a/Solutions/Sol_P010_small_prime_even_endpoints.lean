-- Prove2me | solution 1 for P010.small_prime_even_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:47:47.317243+00:00
-- url     : https://prove2.me/submissions/60ba7fc3-a852-4a70-bf33-a8c03949240a

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_two_mul_prime_mem_class
public import Theorems.Thm_P010_four_mul_prime_mem_class

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p : ℕ) (hp : Nat.Prime p)
    (hsmall : 4 * p ≤ n) :
    2 * p ∈ primeClass n p ∧
      4 * p ∈ primeClass n p ∧ 2 * p ≠ 4 * p := by
  constructor
  · exact two_mul_prime_mem_class n p hp (by omega)
  constructor
  · exact four_mul_prime_mem_class n p hp hsmall
  · have := hp.two_le
    omega
end P010
