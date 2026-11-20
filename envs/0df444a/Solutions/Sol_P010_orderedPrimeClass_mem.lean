-- Prove2me | solution 1 for P010.orderedPrimeClass_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:38:25.385803+00:00
-- url     : https://prove2.me/submissions/5f61be0e-b599-47e8-ae8c-1f4b64f6dcfc

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_Nat_Prime_maxPrimeFac_eq_self
public import Theorems.Thm_Nat_maxPrimeFac_eq_self_iff
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
theorem _root_.solution (n p u v m : ℕ)
    (hu : u ∈ primeClass n p) (hv : v ∈ primeClass n p)
    (hm : m ∈ orderedPrimeClass n p u v) :
    m ∈ primeClass n p := by
  classical
  change m ∈ u :: (((primeClass n p).erase u).erase v).toList ++ [v] at hm
  rcases List.mem_cons.mp hm with heq | ht
  · simpa [heq] using hu
  rcases List.mem_append.mp ht with hmid | hlast
  · exact (Finset.mem_erase.mp
      (Finset.mem_erase.mp (Finset.mem_toList.mp hmid)).2).2
  · have heq : m = v := by simpa using hlast
    simpa [heq] using hv
end P010
