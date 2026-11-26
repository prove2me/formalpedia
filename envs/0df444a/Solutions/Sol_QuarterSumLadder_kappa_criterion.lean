-- Prove2me | solution 1 for QuarterSumLadder.kappa_criterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:28.022827+00:00
-- url     : https://prove2.me/submissions/80738cb2-dcf6-4fb7-9505-240647aa7663

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_quarter_law
public import Theorems.Thm_QuarterSumLadder_kappa_eq
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
attribute [local simp] QuarterSumLadder.gi_im
attribute [local simp] QuarterSumLadder.gi_re



set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution : χ 2 = 1 ↔ kappa p % 4 = (Q p : ℤ) % 4 := by
  have hk := kappa_eq hp8 hχ
  have hq := quarter_law hp8 hχ
  rw [hq, hk]
  rcases Nat.even_or_odd (R χ 1 + R χ 3) with ⟨j, hj⟩ | ⟨j, hj⟩
  · have : ((R χ 1 : ℤ) + R χ 3) = j + j := by exact_mod_cast hj
    rw [hj, Even.neg_one_pow ⟨j, rfl⟩, this]; simp only [true_iff]; omega
  · have : ((R χ 1 : ℤ) + R χ 3) = 2 * j + 1 := by exact_mod_cast hj
    rw [hj, Odd.neg_one_pow ⟨j, rfl⟩, this]
    simp only [show ((-1 : GaussianInt) = 1) ↔ False from ⟨fun h => absurd h (by decide), False.elim⟩,
      false_iff]
    omega
end QuarterSumLadder
