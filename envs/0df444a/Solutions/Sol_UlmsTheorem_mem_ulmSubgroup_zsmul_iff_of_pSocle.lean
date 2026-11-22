-- Prove2me | solution 1 for UlmsTheorem.mem_ulmSubgroup_zsmul_iff_of_pSocle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:59:42.360301+00:00
-- url     : https://prove2.me/submissions/58de3687-80d7-439c-991f-a189cd3dda6c

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
theorem _root_.solution [Fact p.Prime] {g : G}
    (hpg : p • g = 0) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) (β : Ordinal) :
    n • g ∈ ulmSubgroup p β (G := G) ↔ g ∈ ulmSubgroup p β (G := G) := by
  constructor
  · intro hmem
    -- Get Bezout coefficients via Int.gcd_eq_gcd_ab
    have hgcd : Int.gcd n (p : ℤ) = 1 := by
      change n.natAbs.gcd p = 1
      rw [Nat.gcd_comm]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2
        (fun h ↦ hn (Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 h)))
    -- Bezout: n * gcdA + p * gcdB = 1
    have hbez := Int.gcd_eq_gcd_ab n (p : ℤ)
    rw [show (Int.gcd n (p : ℤ) : ℤ) = 1 from by exact_mod_cast hgcd] at hbez
    -- hbez : 1 = n * Int.gcdA n ↑p + ↑p * Int.gcdB n ↑p
    have hg_eq : g = Int.gcdA n ↑p • (n • g) := by
      calc g = (1 : ℤ) • g := (one_zsmul g).symm
        _ = (n * Int.gcdA n ↑p + ↑p * Int.gcdB n ↑p) • g := by rw [← hbez]
        _ = Int.gcdA n ↑p • (n • g) + Int.gcdB n ↑p • ((↑p : ℤ) • g) := by
            rw [add_zsmul, mul_comm n, mul_zsmul, mul_comm (↑p : ℤ), mul_zsmul]
        _ = Int.gcdA n ↑p • (n • g) + Int.gcdB n ↑p • (0 : G) := by
            -- (↑p : ℤ) • g = p • g = 0; congr 2 peels off gcdB • (–)
            congr 2; exact_mod_cast hpg
        _ = Int.gcdA n ↑p • (n • g) := by simp
    rw [hg_eq]
    exact (ulmSubgroup p β (G := G)).zsmul_mem hmem (Int.gcdA n ↑p)
  · exact fun hmem ↦ (ulmSubgroup p β (G := G)).zsmul_mem hmem n
end UlmsTheorem
