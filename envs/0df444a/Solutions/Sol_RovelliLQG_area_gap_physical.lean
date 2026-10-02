-- Prove2me | solution 1 for RovelliLQG.area_gap_physical
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T16:39:20.53126+00:00
-- url     : https://prove2.me/submissions/be8e9d9d-740d-4fb0-ac0c-f0ae1a12a91d

import Mathlib
import Definitions.Def_RovelliLQG_Defs

set_option autoImplicit false

open scoped InnerProductSpace

open RovelliLQG in
theorem e21ba9bb_root_lb (k : ℕ) (hk : k ≠ 0) :
    Real.sqrt 3 / 2 ≤ casimirRoot ((k : ℝ) / 2) := by
  have key : Real.sqrt 3 / 2 = Real.sqrt (3 / 4) := by
    rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4)]
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold casimirRoot
  rw [key]
  apply Real.sqrt_le_sqrt
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  nlinarith

open RovelliLQG in
theorem solution (γ ħ G : ℝ) (hγ : 0 < γ) (hħ : 0 < ħ) (hG : 0 < G) :
    IsLeast {A ∈ areaSpectrum γ ħ G | 0 < A}
      (8 * Real.pi * ħ * G * γ * (Real.sqrt 3 / 2)) := by
  have hc : 0 < 8 * Real.pi * γ * ħ * G := by positivity
  have h1 : casimirRoot ((1 : ℕ) / 2 : ℝ) = Real.sqrt 3 / 2 := by
    unfold casimirRoot
    have : ((1:ℕ):ℝ) / 2 * (((1:ℕ):ℝ) / 2 + 1) = 3 / 4 := by norm_num
    rw [this, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨⟨⟨{1}, ?_⟩, by positivity⟩, ?_⟩
  · simp only [Multiset.map_singleton, Multiset.sum_singleton, h1]
    ring
  · rintro A ⟨⟨ks, rfl⟩, hA⟩
    set S := (ks.map (fun k : ℕ => casimirRoot ((k : ℝ) / 2))).sum with hS
    have hnn : ∀ x ∈ ks.map (fun k : ℕ => casimirRoot ((k : ℝ) / 2)), 0 ≤ x := by
      intro x hx
      obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hx
      exact Real.sqrt_nonneg _
    have hSpos : 0 < S := by
      by_contra h
      have : S ≤ 0 := not_lt.mp h
      have : 8 * Real.pi * γ * ħ * G * S ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc.le this
      linarith
    have hex : ∃ k ∈ ks, k ≠ 0 := by
      by_contra h
      push_neg at h
      have : S = 0 := by
        rw [hS]
        apply Multiset.sum_eq_zero
        intro x hx
        obtain ⟨k, hk, rfl⟩ := Multiset.mem_map.mp hx
        rw [h k hk]
        simp [casimirRoot]
      linarith
    obtain ⟨k, hk, hk0⟩ := hex
    have hle : casimirRoot ((k : ℝ) / 2) ≤ S :=
      Multiset.single_le_sum hnn _ (Multiset.mem_map_of_mem _ hk)
    have hlb := e21ba9bb_root_lb k hk0
    have : Real.sqrt 3 / 2 ≤ S := le_trans hlb hle
    have : 8 * Real.pi * γ * ħ * G * (Real.sqrt 3 / 2) ≤ 8 * Real.pi * γ * ħ * G * S :=
      mul_le_mul_of_nonneg_left this hc.le
    linarith
