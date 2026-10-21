-- Prove2me | solution 1 for PerimeterPatrol.Visible.blue_red_count
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T22:46:59.378675+00:00
-- url     : https://prove2.me/submissions/63827202-e193-4eca-a864-19bd7e857c9e

import Mathlib
import Definitions.Def_PerimeterPatrol_Visible_Model
import Definitions.Def_PerimeterPatrol_Visible_OptimalPatrol

namespace PerimeterPatrol.Visible

lemma PP_slot_iff (t b : ℝ) (ht : 0 < t) (hb : -t ≤ b) (j : ℕ) :
    (b < (j : ℝ) * t ∧ (j : ℝ) * t ≤ b + t) ↔ j = ⌊b / t + 1⌋₊ := by
  have hx : 0 ≤ b / t + 1 := by
    have : -1 ≤ b / t := by rw [le_div_iff₀ ht]; linarith
    linarith
  have e1 : b < (j : ℝ) * t ↔ b / t + 1 < (j : ℝ) + 1 := by
    rw [add_lt_add_iff_right, div_lt_iff₀ ht]
  have e2 : (j : ℝ) * t ≤ b + t ↔ (j : ℝ) ≤ b / t + 1 := by
    rw [show b / t + 1 = (b + t) / t by field_simp]; rw [le_div_iff₀ ht]
  rw [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    apply le_antisymm (Nat.le_floor h2)
    have := Nat.floor_le hx
    have : (⌊b / t + 1⌋₊ : ℝ) < (j : ℝ) + 1 := by linarith
    exact_mod_cast Nat.lt_add_one_iff.mp (by exact_mod_cast this)
  · rintro rfl
    exact ⟨Nat.lt_floor_add_one _, Nat.floor_le hx⟩

end PerimeterPatrol.Visible

open PerimeterPatrol.Visible in
theorem solution (lam t a : ℝ) (hlam : 0 < lam) (ht : 0 < t) (ha : 0 ≤ a) : Nat.card {jk : ℕ × ℕ | IsBlue lam t jk ∧ a < bluePoint lam t jk ∧ bluePoint lam t jk ≤ a + t} = ⌊lam * t⌋₊ ∧ Nat.card {j : ℕ | a < (j : ℝ) * t ∧ (j : ℝ) * t ≤ a + t} = 1 := by
  constructor
  · set n := ⌊lam * t⌋₊ with hn
    set D := t / (⌈lam * t⌉₊ : ℝ) with hD
    have hc : (0 : ℝ) < ⌈lam * t⌉₊ := by
      have : 0 < ⌈lam * t⌉₊ := Nat.ceil_pos.mpr (by positivity)
      exact_mod_cast this
    have hkD : ∀ k : ℕ, k ≤ n → (k : ℝ) * D ≤ t := by
      intro k hk
      have : (k : ℝ) ≤ ⌈lam * t⌉₊ := by
        exact_mod_cast le_trans hk (Nat.floor_le_ceil _)
      rw [hD, mul_div_assoc', div_le_iff₀ hc]; nlinarith
    let g : ℕ → ℕ × ℕ := fun k => (⌊(a - (k : ℝ) * D) / t + 1⌋₊, k)
    have hg : Function.Injective g := by
      intro x y h; simpa [g] using congrArg Prod.snd h
    have hset : {jk : ℕ × ℕ | IsBlue lam t jk ∧ a < bluePoint lam t jk ∧ bluePoint lam t jk ≤ a + t}
        = ↑((Finset.Icc 1 n).image g) := by
      ext ⟨j, k⟩
      simp only [Set.mem_setOf_eq, IsBlue, bluePoint, Finset.coe_image, Finset.coe_Icc,
        Set.mem_image, Set.mem_Icc, g, Prod.mk.injEq]
      rw [← hD, ← hn]
      constructor
      · rintro ⟨⟨hk1, hk2⟩, h1, h2⟩
        refine ⟨k, ⟨hk1, hk2⟩, ?_, rfl⟩
        have hb : -t ≤ a - (k : ℝ) * D := by linarith [hkD k hk2]
        exact ((PP_slot_iff t (a - (k : ℝ) * D) ht hb j).mp ⟨by linarith, by linarith⟩).symm
      · rintro ⟨k', ⟨hk1, hk2⟩, hj, rfl⟩
        have hb : -t ≤ a - (k' : ℝ) * D := by linarith [hkD k' hk2]
        have := (PP_slot_iff t (a - (k' : ℝ) * D) ht hb j).mpr hj.symm
        exact ⟨⟨hk1, hk2⟩, by linarith [this.1], by linarith [this.2]⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ hg]
    simp
  · have hset : {j : ℕ | a < (j : ℝ) * t ∧ (j : ℝ) * t ≤ a + t} = {⌊a / t + 1⌋₊} := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact PP_slot_iff t a ht (by linarith) j
    rw [hset]; simp
