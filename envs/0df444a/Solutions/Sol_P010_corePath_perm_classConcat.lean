-- Prove2me | solution 1 for P010.corePath_perm_classConcat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:54:25.465979+00:00
-- url     : https://prove2.me/submissions/9d27b315-8f32-4eb9-9bd4-400915c1970d

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_splitPrimePairs_recompose
public import Theorems.Thm_P010_splitPrimePairs_pair_mem
public import Theorems.Thm_P010_splitPrimePairs_spare_mem
public import Theorems.Thm_P010_classConcat_congr_perm
public import Theorems.Thm_P010_coreIndices_perm
public import Theorems.Thm_P010_threeEvenUnit_none_perm
public import Theorems.Thm_P010_threeEvenUnit_some_perm
public import Theorems.Thm_P010_intermediateUnits_perm
public import Theorems.Thm_P010_smallUnits_perm
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
    (corePath n).Perm (classConcat n (n / 3).primesLE.toList) := by
  classical
  let mids := (intermediatePrimes n).toList
  let sp := splitPrimePairs mids
  let small := ((n / 4).primesLE.erase 3).toList
  let pairIdx := sp.1.flatMap (fun pq => [pq.1, pq.2])

  have hthree : (threeEvenUnit n sp.2).Perm
      (classConcat n (3 :: sp.2.toList)) := by
    cases hopt : sp.2 with
    | none =>
        simpa [hopt] using threeEvenUnit_none_perm n hn
    | some p =>
        have hp : p ∈ intermediatePrimes n := by
          apply Finset.mem_toList.mp
          exact splitPrimePairs_spare_mem mids p (by simpa [sp, mids] using hopt)
        simpa [hopt] using threeEvenUnit_some_perm n p hn hp

  have hsmall : ∀ p ∈ small, Nat.Prime p ∧ 4 * p ≤ n := by
    intro p hp
    have hmem : p ∈ (n / 4).primesLE :=
      (Finset.mem_erase.mp (Finset.mem_toList.mp hp)).2
    obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp hmem
    exact ⟨hprime, by omega⟩
  have hsmallPerm : (small.map (smallEvenUnit n)).flatten.Perm
      (classConcat n small) :=
    smallUnits_perm n small hsmall

  have hpairs : ∀ pq ∈ sp.1,
      pq.1 ∈ intermediatePrimes n ∧ pq.2 ∈ intermediatePrimes n := by
    intro pq hp
    obtain ⟨hp1, hp2⟩ :=
      splitPrimePairs_pair_mem mids pq (by simpa [sp, mids] using hp)
    exact ⟨Finset.mem_toList.mp hp1, Finset.mem_toList.mp hp2⟩
  have hpairsPerm : (sp.1.map (intermediateEvenUnit n)).flatten.Perm
      (classConcat n pairIdx) := by
    simpa [pairIdx] using intermediateUnits_perm n sp.1 hn hpairs

  have hsum : (corePath n).Perm
      (classConcat n ((3 :: sp.2.toList) ++ small ++ pairIdx)) := by
    have hh := hthree.append (hsmallPerm.append hpairsPerm)
    simpa [corePath, coreUnits, mids, sp, small, pairIdx,
      classConcat, List.flatMap_append, List.flatten_append,
      List.map_append, List.append_assoc] using hh

  have hrecompose : pairIdx ++ sp.2.toList = mids := by
    simpa [pairIdx, sp, mids] using splitPrimePairs_recompose mids
  have hindices : ((3 :: sp.2.toList) ++ small ++ pairIdx).Perm
      (coreIndices n) := by
    have hswap : (sp.2.toList ++ (small ++ pairIdx)).Perm
        ((small ++ pairIdx) ++ sp.2.toList) := List.perm_append_comm
    have hswap' : (sp.2.toList ++ small ++ pairIdx).Perm
        (small ++ mids) := by
      simpa [List.append_assoc, hrecompose] using hswap
    simpa [coreIndices, small, mids, List.append_assoc] using
      hswap'.cons 3

  have hcore : (corePath n).Perm (classConcat n (coreIndices n)) :=
    hsum.trans (classConcat_congr_perm n _ _ hindices)
  exact hcore.trans (classConcat_congr_perm n _ _
    (coreIndices_perm n hn))
end P010
