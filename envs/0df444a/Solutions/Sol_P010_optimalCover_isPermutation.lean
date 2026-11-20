-- Prove2me | solution 1 for P010.optimalCover_isPermutation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:55:55.508332+00:00
-- url     : https://prove2.me/submissions/e7cfa041-2225-42e2-b1b1-1e2603f9741b

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_classConcat_congr_perm
public import Theorems.Thm_P010_classConcat_all_primes
public import Theorems.Thm_P010_range_one_perm_Icc
public import Theorems.Thm_P010_corePath_perm_classConcat
public import Theorems.Thm_P010_packLeafClasses_perm
public import Theorems.Thm_P010_leafClasses_perm
public import Theorems.Thm_P010_largeSingletons_perm
public import Theorems.Thm_P010_segments_index_perm
public import Theorems.Thm_P010_one_Icc_two_perm_Icc_one
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
    IsPermutation n (optimalCover n).flatten := by
  classical
  let big := (largePrimes n).toList
  let small := (n / 3).primesLE.toList
  let leaves := (middlePrimes n).toList

  have hlarge : (big.map (fun p => [p])).flatten.Perm
      (classConcat n big) := largeSingletons_perm n

  have hmiddle : ∀ p ∈ leaves, p ∈ middlePrimes n := by
    intro p hp
    exact Finset.mem_toList.mp hp
  have hleaf := leafClasses_perm n leaves hmiddle
  have hcore := corePath_perm_classConcat n hn
  have hpack : (packLeafClasses (corePath n) leaves).flatten.Perm
      (classConcat n small ++ classConcat n leaves) := by
    have hpreserve := packLeafClasses_perm (corePath n) leaves
    exact hpreserve.trans (hcore.append hleaf)

  have hall : (optimalCover n).flatten.Perm
      (1 :: (classConcat n big ++
        (classConcat n small ++ classConcat n leaves))) := by
    have h := (hlarge.append hpack).append_left [1]
    simpa [optimalCover, big, small, leaves,
      List.flatten_append, List.map_append,
      List.append_assoc] using h

  have hind : (big ++ small ++ leaves).Perm n.primesLE.toList := by
    have hswap : (big ++ (small ++ leaves)).Perm
        ((small ++ leaves) ++ big) := List.perm_append_comm
    have hrest := segments_index_perm n
    simpa [big, small, leaves, List.append_assoc] using
      hswap.trans hrest

  have hcat : (classConcat n big ++
        (classConcat n small ++ classConcat n leaves)).Perm
        (classConcat n n.primesLE.toList) := by
    simpa [classConcat, List.flatMap_append, List.append_assoc] using
      classConcat_congr_perm n (big ++ small ++ leaves)
        n.primesLE.toList hind

  have hfull : (optimalCover n).flatten.Perm
      (1 :: (Finset.Icc 2 n).toList) :=
    hall.trans ((hcat.trans (classConcat_all_primes n)).cons 1)

  have htwo := one_Icc_two_perm_Icc_one n (by omega)
  have hrange := range_one_perm_Icc n
  exact hfull.trans htwo |>.trans hrange.symm
end P010
