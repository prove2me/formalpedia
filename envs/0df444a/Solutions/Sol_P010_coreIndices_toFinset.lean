-- Prove2me | solution 1 for P010.coreIndices_toFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:50:42.762939+00:00
-- url     : https://prove2.me/submissions/b54a33c4-8fb3-4dbe-a6fa-e4be0d3d9229

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_small_intermediate_partition
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
    (coreIndices n).toFinset = (n / 3).primesLE := by
  classical
  have hthree : 3 ∈ (n / 4).primesLE :=
    Nat.mem_primesLE.mpr ⟨by omega, by norm_num⟩
  have hclean : insert 3 ((n / 4).primesLE.erase 3) =
      (n / 4).primesLE := Finset.insert_erase hthree
  rw [coreIndices]
  simp only [List.toFinset_cons, List.toFinset_append,
    Finset.toList_toFinset]
  rw [← Finset.insert_union]
  rw [hclean]
  exact small_intermediate_partition n
end P010
