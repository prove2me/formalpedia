-- Prove2me | solution 1 for SemigroupBetti.GenData.exc_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:14:26.872077+00:00
-- url     : https://prove2.me/submissions/a1f30272-c536-459b-930f-ddb47664c758

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_b_eq
public import Theorems.Thm_SemigroupBetti_GenData_gcd_m_g
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_three_le_W
public import Theorems.Thm_SemigroupBetti_GenData_w_eq
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
variable {G}
variable (hA : G.A = 1) (hB : G.B = G.W - 1)
include hA hB
set_option linter.unusedSectionVars false
namespace SemigroupBetti.GenData
theorem _root_.solution : Nat.Coprime (G.n 3) (G.n 2) := by
  have hW := G.three_le_W
  have hn2 : G.n 2 = G.m + G.g * (G.W - 1) := by rw [n_two, G.b_eq, hB]
  have hn3 : G.n 3 = G.n 2 + G.g := by
    rw [hn2, n_three, G.w_eq]
    have : G.W = (G.W - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  set k := Nat.gcd (G.n 3) (G.n 2)
  have hk3 : k ∣ G.n 3 := Nat.gcd_dvd_left _ _
  have hk2 : k ∣ G.n 2 := Nat.gcd_dvd_right _ _
  have hkg : k ∣ G.g := by
    rw [hn3] at hk3; exact (Nat.dvd_add_right hk2).1 hk3
  have hkm : k ∣ G.m := by
    rw [hn2] at hk2
    exact (Nat.dvd_add_left (Dvd.dvd.mul_right hkg _)).1 hk2
  have := Nat.dvd_gcd hkm hkg
  rw [G.gcd_m_g] at this
  exact Nat.dvd_one.1 this
end SemigroupBetti.GenData
