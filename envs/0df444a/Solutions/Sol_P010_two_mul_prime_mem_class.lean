-- Prove2me | solution 1 for P010.two_mul_prime_mem_class
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:31:15.10724+00:00
-- url     : https://prove2.me/submissions/456687e0-0470-426e-95ca-db448dd475d2

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_mem_primeClass
public import Theorems.Thm_Nat_Prime_maxPrimeFac_eq_self
public import Theorems.Thm_Nat_maxPrimeFac_mul
attribute [local simp] Nat.Prime.maxPrimeFac_eq_self



set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p : ℕ) (hp : Nat.Prime p)
    (hpn : 2 * p ≤ n) : 2 * p ∈ primeClass n p := by
  have hp2 := hp.two_le
  have hmax : Nat.maxPrimeFac (2 * p) = p := by
    rw [Nat.maxPrimeFac_mul (by omega) hp.ne_zero,
      (Nat.Prime.maxPrimeFac_eq_self (by norm_num : Nat.Prime 2)), hp.maxPrimeFac_eq_self]
    exact max_eq_right hp.two_le
  exact mem_primeClass.mpr ⟨by omega, hpn, hmax⟩
end P010
