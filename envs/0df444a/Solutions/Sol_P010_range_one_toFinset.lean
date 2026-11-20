-- Prove2me | solution 1 for P010.range_one_toFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:49:23.883267+00:00
-- url     : https://prove2.me/submissions/accc5e4b-7db8-45f4-a2ec-82da166e8753

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
theorem _root_.solution (n : ℕ) :
    (List.range' 1 n).toFinset = Finset.Icc 1 n := by
  classical
  ext m
  simp only [List.mem_toFinset, Finset.mem_Icc]
  constructor
  · intro hm
    obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hm
    omega
  · rintro ⟨hpos, hle⟩
    apply List.mem_range'.mpr
    refine ⟨m - 1, by omega, ?_⟩
    omega
end P010
