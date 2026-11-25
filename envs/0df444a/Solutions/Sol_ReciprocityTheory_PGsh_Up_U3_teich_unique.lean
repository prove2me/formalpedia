-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.teich_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:48:09.002082+00:00
-- url     : https://prove2.me/submissions/f6dfbd5c-23b8-4292-b2a8-abf7860a97c1

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_v_le_one_of_pow_eq
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_v_pow_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution (hv : v.Integers R) (hpv : v (p : C) < 1) {r s : C} (hr : r ^ p = r)
    (hs : s ^ p = s) (h : v (r - s) < 1) : r = s := by
  by_contra hne
  have hd : r - s ≠ 0 := sub_ne_zero.mpr hne
  have hr1 : v r ≤ 1 := v_le_one_of_pow_eq hr
  have hs1 : v s ≤ 1 := v_le_one_of_pow_eq hs
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ k ∈ range p, r ^ k * s ^ (p - 1 - k) := ⟨_, rfl⟩
  have hSd : S * (r - s) = r - s := by rw [hS, geom_sum₂_mul, hr, hs]
  have hS1 : S = 1 := mul_right_cancel₀ hd (by rw [hSd, one_mul])
  have hconst : ∑ k ∈ range p, s ^ k * s ^ (p - 1 - k) = (p : C) * s ^ (p - 1) := by
    rw [Finset.sum_congr rfl (g := fun _ => s ^ (p - 1)) (fun k hk => by
      rw [← pow_add]
      congr 1
      have := Finset.mem_range.mp hk
      omega)]
    simp
  have hdiff : S - (p : C) * s ^ (p - 1) = ∑ k ∈ range p, (r ^ k - s ^ k) * s ^ (p - 1 - k) := by
    rw [← hconst, hS, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hlt1 : v (S - (p : C) * s ^ (p - 1)) < 1 := by
    rw [hdiff]
    apply v.map_sum_lt one_ne_zero
    intro k _
    rw [map_mul]
    calc v (r ^ k - s ^ k) * v (s ^ (p - 1 - k)) ≤ v (r ^ k - s ^ k) * 1 :=
          mul_le_mul_of_nonneg_left (by rw [map_pow]; exact pow_le_one₀ zero_le' hs1) zero_le'
      _ ≤ v (r - s) := by rw [mul_one]; exact v_pow_sub_le hr1 hs1 k
      _ < 1 := h
  have hlt2 : v ((p : C) * s ^ (p - 1)) < 1 := by
    rw [map_mul, map_pow]
    calc v (p : C) * v s ^ (p - 1) ≤ v (p : C) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ zero_le' hs1) zero_le'
      _ < 1 := by rw [mul_one]; exact hpv
  have hv : v S < 1 := by
    have := v.map_add_lt hlt1 hlt2
    rwa [sub_add_cancel] at this
  rw [hS1, map_one] at hv
  exact lt_irrefl _ hv
end ReciprocityTheory.PGsh.Up.U3
