-- Prove2me | solution 1 for P010.segments_index_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:52:35.634647+00:00
-- url     : https://prove2.me/submissions/9697fb75-9eb5-49dc-9845-1ec4b7fc9d8f

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_mem_largePrimes
public import Theorems.Thm_P010_mem_middlePrimes
public import Theorems.Thm_P010_prime_segments_partition
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
    ((n / 3).primesLE.toList ++
      (middlePrimes n).toList ++
      (largePrimes n).toList).Perm n.primesLE.toList := by
  classical
  have hn : (((n / 3).primesLE.toList ++
      (middlePrimes n).toList) ++
      (largePrimes n).toList).Nodup := by
    apply List.nodup_append'.mpr
    constructor
    · apply List.nodup_append'.mpr
      refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
      apply List.disjoint_left.mpr
      intro p hp hq
      have hle := (Nat.mem_primesLE.mp (Finset.mem_toList.mp hp)).1
      have hgt := (mem_middlePrimes.mp (Finset.mem_toList.mp hq)).2.1
      omega
    constructor
    · exact Finset.nodup_toList _
    · apply List.disjoint_left.mpr
      intro p hp hq
      have hbig := (mem_largePrimes.mp (Finset.mem_toList.mp hq)).2.1
      rcases List.mem_append.mp hp with hs | hm
      · have hle := (Nat.mem_primesLE.mp (Finset.mem_toList.mp hs)).1
        omega
      · have hle := (mem_middlePrimes.mp (Finset.mem_toList.mp hm)).2.2
        omega
  apply List.perm_of_nodup_nodup_toFinset_eq
    (by simpa [List.append_assoc] using hn) (Finset.nodup_toList _)
  simp only [List.toFinset_append, Finset.toList_toFinset]
  simpa [Finset.union_assoc] using prime_segments_partition n
end P010
