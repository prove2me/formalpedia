-- Prove2me | solution 1 for P010.three_mul_prime_mem_class
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:33:08.414435+00:00
-- url     : https://prove2.me/submissions/bad48567-aef6-48ff-88bd-0fee0713bfc4

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
    (hp3 : 3 ≤ p) (hpn : 3 * p ≤ n) :
    3 * p ∈ primeClass n p := by
  have hp2 := hp.two_le
  have hmax : Nat.maxPrimeFac (3 * p) = p := by
    rw [Nat.maxPrimeFac_mul (by omega) hp.ne_zero,
      (Nat.Prime.maxPrimeFac_eq_self (by norm_num : Nat.Prime 3)), hp.maxPrimeFac_eq_self]
    exact max_eq_right hp3
  exact mem_primeClass.mpr ⟨by omega, hpn, hmax⟩
end P010
