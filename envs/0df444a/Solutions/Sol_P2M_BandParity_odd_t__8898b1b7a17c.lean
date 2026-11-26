-- Prove2me | solution 1 for P2M_BandParity_odd_t__8898b1b7a17c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:23.655124+00:00
-- url     : https://prove2.me/submissions/b7ac6266-14c6-4502-b2a3-f3b9f8ebff0e

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
public import Theorems.Thm_BandParity_S_add_S_neg
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) (hp5 : 5 < p) : Odd (t χ) := by
  have h := S_add_S_neg hχ hp8 hp5 gi (by simp)
  rw [t, show S χ (-gi) = ((p - 1) / 4 : ℕ) - S χ gi by linarith]
  have : Odd (((p - 1) / 4 : ℕ) : ℤ) := by
    rw [Int.odd_coe_nat]; exact Nat.odd_iff.2 (by omega)
  obtain ⟨j, hj⟩ := this
  exact ⟨S χ gi - j - 1, by linarith⟩
end BandParity
