-- Prove2me | solution 1 for P010.coreIndices_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:49:22.273924+00:00
-- url     : https://prove2.me/submissions/98be534e-c0eb-428b-b6a7-0eb7ebb116db

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_mem_intermediatePrimes
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
theorem _root_.solution (n : ℕ) (hn : 12 ≤ n) :
    (coreIndices n).Nodup := by
  classical
  unfold coreIndices
  apply List.nodup_cons.mpr
  constructor
  · simp only [List.mem_append, Finset.mem_toList, Finset.mem_erase,
        not_or]
    constructor
    · simp
    · intro hm
      have hgt := (mem_intermediatePrimes.mp hm).2.1
      omega
  · apply List.nodup_append'.mpr
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
    apply List.disjoint_left.mpr
    intro p hp hq
    have hsmall : p ≤ n / 4 :=
      (Nat.mem_primesLE.mp
        (Finset.mem_erase.mp (Finset.mem_toList.mp hp)).2).1
    have hlarge : n / 4 < p :=
      (mem_intermediatePrimes.mp (Finset.mem_toList.mp hq)).2.1
    omega
end P010
