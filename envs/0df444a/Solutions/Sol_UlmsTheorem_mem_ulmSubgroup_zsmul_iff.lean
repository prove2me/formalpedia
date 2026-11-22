-- Prove2me | solution 1 for UlmsTheorem.mem_ulmSubgroup_zsmul_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:57:58.759614+00:00
-- url     : https://prove2.me/submissions/138cb964-7df7-40ef-bc68-f6a2d3b766a9

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero


attribute [local simp] UlmsTheorem.pOrder_zero

set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ)
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
namespace UlmsTheorem
theorem _root_.solution [Fact p.Prime] (hprim : IsPrimaryPGroup p G)
    {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) (u : G) (β : Ordinal.{0}) :
    n • u ∈ ulmSubgroup p β (G := G) ↔ u ∈ ulmSubgroup p β (G := G) := by
  constructor
  · intro hmem
    obtain ⟨k, hk⟩ := hprim u
    -- `n` is prime to `p^k`, so Bezout inverts it on `u`
    have hcop : IsCoprime (n : ℤ) ((p : ℤ) ^ k) := by
      exact (Int.isCoprime_iff_gcd_eq_one.mpr (by
        have : Int.gcd n (p : ℤ) = 1 := by
          change n.natAbs.gcd p = 1
          rw [Nat.gcd_comm]
          exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2
            (fun h ↦ hn (Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 h)))
        exact this)).pow_right
    obtain ⟨a, b, hab⟩ := hcop
    have hu : u = a • (n • u) := by
      calc u = (1 : ℤ) • u := (one_zsmul u).symm
        _ = (a * n + b * (p : ℤ) ^ k) • u := by rw [hab]
        _ = a • (n • u) + b • (((p : ℤ) ^ k) • u) := by
            rw [add_zsmul, mul_zsmul, mul_zsmul]
        _ = a • (n • u) + b • (0 : G) := by
            congr 2
            have : (((p : ℤ) ^ k) • u) = (p ^ k : ℕ) • u := by
              rw [← Int.natCast_pow, natCast_zsmul]
            rw [this, hk]
        _ = a • (n • u) := by simp
    rw [hu]
    exact (ulmSubgroup p β).zsmul_mem hmem a
  · intro hmem
    exact (ulmSubgroup p β).zsmul_mem hmem n
end UlmsTheorem
