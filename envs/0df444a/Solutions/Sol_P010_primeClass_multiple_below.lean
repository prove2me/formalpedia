-- Prove2me | solution 1 for P010.primeClass_multiple_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:39:59.030341+00:00
-- url     : https://prove2.me/submissions/2f1d59d1-e85d-4e32-aa88-30ee122499ba

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_mem_primeClass
public import Theorems.Thm_P010_primeClass_dvd
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
theorem _root_.solution (n p m k : ℕ)
    (hm : m ∈ primeClass n p) (hupper : n < k * p) :
    ∃ t : ℕ, 1 ≤ t ∧ t < k ∧ m = t * p := by
  obtain ⟨t, ht⟩ := primeClass_dvd hm
  have hpos : 2 ≤ m := (mem_primeClass.mp hm).1
  have hle : m ≤ n := (mem_primeClass.mp hm).2.1
  have htp : m = t * p := by simpa [Nat.mul_comm] using ht
  have htpos : 1 ≤ t := by
    by_contra h
    have hzero : t = 0 := by omega
    subst t
    simp at htp
    omega
  have htlt : t < k := by
    by_contra h
    have hge : k ≤ t := by omega
    have hprod : k * p ≤ t * p := Nat.mul_le_mul_right p hge
    omega
  exact ⟨t, htpos, htlt, htp⟩
end P010
