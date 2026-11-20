-- Prove2me | solution 1 for P010.primeClass_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:45:41.003919+00:00
-- url     : https://prove2.me/submissions/1089cfa9-e4fa-4152-bc27-eb2728d8b9bb

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_mem_primeClass
public import Theorems.Thm_Nat_maxPrimeFac_le
public import Theorems.Thm_Nat_prime_maxPrimeFac_of_one_lt


set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) :
    (n.primesLE.biUnion (fun p => primeClass n p)) = Finset.Icc 2 n := by
  ext m
  constructor
  · intro hm
    obtain ⟨p, _, hmp⟩ := Finset.mem_biUnion.mp hm
    have h := mem_primeClass.mp hmp
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩
  · intro hm
    have hr := Finset.mem_Icc.mp hm
    have hprime : Nat.Prime (Nat.maxPrimeFac m) :=
      Nat.prime_maxPrimeFac_of_one_lt (by omega)
    have hle : Nat.maxPrimeFac m ≤ n :=
      (Nat.maxPrimeFac_le (n := m)).trans hr.2
    apply Finset.mem_biUnion.mpr
    refine ⟨Nat.maxPrimeFac m, ?_, ?_⟩
    · exact Nat.mem_primesLE.mpr ⟨hle, hprime⟩
    · exact mem_primeClass.mpr ⟨hr.1, hr.2, rfl⟩
end P010
