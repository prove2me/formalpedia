-- Prove2me | solution 1 for P010.append_even_ended
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:47:33.586183+00:00
-- url     : https://prove2.me/submissions/c707af1d-8b58-404d-925d-b5c7b42d07cf

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_join_even_ended_paths
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
theorem _root_.solution (a b : List ℕ)
    (ha : NonCoprimeChain a) (hb : NonCoprimeChain b)
    (hea : EvenEnded a) (heb : EvenEnded b) :
    NonCoprimeChain (a ++ b) ∧ EvenEnded (a ++ b) := by
  obtain ⟨u, v, hau, hav, hu, hv⟩ := hea
  obtain ⟨w, z, hbw, hbz, hw, hz⟩ := heb
  have hchain : NonCoprimeChain (a ++ b) := by
    apply join_even_ended_paths a b ha hb
    · intro x hx
      have heq : v = x := by simpa [hav] using hx
      simpa [← heq] using hv
    · intro y hy
      have heq : w = y := by simpa [hbw] using hy
      simpa [← heq] using hw
  have hane : a ≠ [] := by
    intro h
    simp [h] at hau
  have hbne : b ≠ [] := by
    intro h
    simp [h] at hbw
  refine ⟨hchain, u, z, ?_, ?_, hu, hz⟩
  · rw [List.head?_append_of_ne_nil a hane, hau]
  · rw [List.getLast?_append_of_ne_nil a hbne, hbz]
end P010
