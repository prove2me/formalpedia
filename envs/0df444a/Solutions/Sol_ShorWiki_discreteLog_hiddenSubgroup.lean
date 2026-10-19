-- Prove2me | solution 1 for ShorWiki.discreteLog_hiddenSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:39:09.713873+00:00
-- url     : https://prove2.me/submissions/65702d5d-26d2-4eeb-94a1-54e259c4d309

import Mathlib
import Definitions.Def_ShorWiki_Defs
open ShorWiki

namespace ShorDLog

lemma f_eq {G : Type*} [Group G] (g : G) (r : ℕ) (x y : ℕ) :
    g ^ x * ((g ^ r) ^ y)⁻¹ = g ^ ((x : ℤ) - r * y) := by
  rw [zpow_sub, zpow_natCast, ← pow_mul,
    show (r : ℤ) * y = ((r * y : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

end ShorDLog

open ShorDLog in
theorem solution {G : Type*} [Group G] [Fintype G] (g : G)
    (hg : ∀ h : G, h ∈ Subgroup.zpowers g) (r : ℕ) :
    (∀ a b a' b' : ZMod (Fintype.card G),
        g ^ (a + a').val * ((g ^ r) ^ (b + b').val)⁻¹
          = (g ^ a.val * ((g ^ r) ^ b.val)⁻¹) * (g ^ a'.val * ((g ^ r) ^ b'.val)⁻¹)) ∧
    ∀ a b : ZMod (Fintype.card G),
      g ^ a.val * ((g ^ r) ^ b.val)⁻¹ = 1 ↔
        ∃ t : ZMod (Fintype.card G), a = t * (r : ZMod (Fintype.card G)) ∧ b = t := by
  set n := Fintype.card G with hn
  have hord : orderOf g = n := by
    rw [hn, ← Nat.card_eq_fintype_card]; exact orderOf_eq_card_of_forall_mem_zpowers hg
  -- g ^ k = g ^ k' iff k ≡ k' in ZMod n
  have key : ∀ k k' : ℤ, ((k : ZMod n) = k') → g ^ k = g ^ k' := by
    intro k k' h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
    have : g ^ (k' - k) = 1 := by rw [← orderOf_dvd_iff_zpow_eq_one, hord]; exact_mod_cast h
    rw [zpow_sub, mul_inv_eq_one] at this
    exact this.symm
  have hval : ∀ x : ZMod n, (((x.val : ℕ) : ℤ) : ZMod n) = x := by
    intro x; push_cast; exact ZMod.natCast_zmod_val x
  refine ⟨fun a b a' b' => ?_, fun a b => ?_⟩
  · simp only [f_eq]
    rw [← zpow_add]
    apply key
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  · rw [f_eq, ← orderOf_dvd_iff_zpow_eq_one, hord, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    constructor
    · intro h; exact ⟨by linear_combination h, rfl⟩
    · intro h; linear_combination h.1
