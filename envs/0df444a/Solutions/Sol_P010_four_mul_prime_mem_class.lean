-- Prove2me | solution 1 for P010.four_mul_prime_mem_class
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:46:19.034195+00:00
-- url     : https://prove2.me/submissions/e733d451-b15d-4d12-a9a6-2e1a2ba7367a

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_mem_primeClass
public import Theorems.Thm_Nat_Prime_maxPrimeFac_eq_self
public import Theorems.Thm_Nat_maxPrimeFac_eq_self_iff
public import Theorems.Thm_Nat_maxPrimeFac_mul
public import Theorems.Thm_Nat_maxPrimeFac_one
public import Theorems.Thm_Nat_maxPrimeFac_pow
public import Theorems.Thm_Nat_maxPrimeFac_zero
public import Theorems.Thm_Nat_one_le_maxPrimeFac_iff
public import Theorems.Thm_Nat_one_lt_maxPrimeFac_iff
attribute [local simp] Nat.Prime.maxPrimeFac_eq_self
attribute [local simp] Nat.maxPrimeFac_eq_self_iff
attribute [local simp] Nat.maxPrimeFac_one
attribute [local simp] Nat.maxPrimeFac_pow
attribute [local simp] Nat.maxPrimeFac_zero
attribute [local simp] Nat.one_le_maxPrimeFac_iff
attribute [local simp] Nat.one_lt_maxPrimeFac_iff



set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p : ℕ) (hp : Nat.Prime p)
    (hpn : 4 * p ≤ n) : 4 * p ∈ primeClass n p := by
  have hp2 := hp.two_le
  have hmax : Nat.maxPrimeFac (4 * p) = p := by
    rw [Nat.maxPrimeFac_mul (by omega) hp.ne_zero,
      (show Nat.maxPrimeFac 4 = 2 by
        have h2 : Nat.maxPrimeFac 2 = 2 :=
          Nat.Prime.maxPrimeFac_eq_self (by norm_num : Nat.Prime 2)
        have hh := Nat.maxPrimeFac_mul (m := 2) (n := 2)
          (by norm_num) (by norm_num)
        simpa [h2] using hh), hp.maxPrimeFac_eq_self]
    exact max_eq_right hp.two_le
  exact mem_primeClass.mpr ⟨by omega, hpn, hmax⟩
end P010
