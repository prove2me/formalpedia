-- Prove2me | solution 1 for QuarticPairing.conj_eq_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:35:49.172163+00:00
-- url     : https://prove2.me/submissions/d2d157bb-4008-493e-9be7-f7a405c13b6d

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
public import Theorems.Thm_QuarticPairing_mul_conj_self_eq_one

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution {g ξ : ℂ} {k : ℕ} (hk : 1 ≤ k) (hg : ‖g‖ = 1) (h : g ^ k = ξ) :
    starRingEnd ℂ g = g ^ (k - 1) * starRingEnd ℂ ξ := by
  have hgg := mul_conj_self_eq_one hg
  rw [← h, map_pow]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ (starRingEnd ℂ g) j, ← mul_assoc, ← mul_pow, hgg, one_pow,
    one_mul]
end QuarticPairing
