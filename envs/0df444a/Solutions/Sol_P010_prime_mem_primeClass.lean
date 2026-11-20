-- Prove2me | solution 1 for P010.prime_mem_primeClass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:33:07.644185+00:00
-- url     : https://prove2.me/submissions/7eb52bda-5daf-4861-bdc5-a7f4b826bb2a

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_mem_primeClass
public import Theorems.Thm_Nat_Prime_maxPrimeFac_eq_self
attribute [local simp] Nat.Prime.maxPrimeFac_eq_self



set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p : ℕ) (hp : Nat.Prime p)
    (hpn : p ≤ n) : p ∈ primeClass n p := by
  exact mem_primeClass.mpr
    ⟨hp.two_le, hpn, hp.maxPrimeFac_eq_self⟩
end P010
