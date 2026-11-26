-- Prove2me | solution 1 for P2M_BandParity_odd_k__12c0ba03e16b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:22.17638+00:00
-- url     : https://prove2.me/submissions/4937bd7e-bc82-4aee-bddb-973c4a93b133

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
theorem _root_.solution (hp8 : p % 8 = 5) (hp5 : 5 < p) : Odd (k χ) := by
  have h := S_add_S_neg hχ hp8 hp5 1 (by simp)
  rw [k, show S χ (-1) = ((p - 1) / 4 : ℕ) - S χ 1 by linarith]
  have : Odd (((p - 1) / 4 : ℕ) : ℤ) := by
    rw [Int.odd_coe_nat]; exact Nat.odd_iff.2 (by omega)
  obtain ⟨j, hj⟩ := this
  exact ⟨S χ 1 - j - 1, by linarith⟩
end BandParity
