-- Prove2me | solution 1 for StrategicInventory.Sequential.inventory_near_five_sixths
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T13:59:47.548792+00:00
-- url     : https://prove2.me/submissions/3d8b2e6a-b473-40f8-a88a-dbcfec2d2072
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StrategicInventory_Sequential_Game
import Definitions.Def_StrategicInventory_Sequential_IsSPE
import Definitions.Def_StrategicInventory_Sequential_Thresholds
import Theorems.Thm_StrategicInventory_Sequential_region7_path
import Theorems.Thm_StrategicInventory_Sequential_region8_path

set_option autoImplicit false

namespace StrategicInventory.Sequential

namespace SI1

lemma s3_lt : s3 1 < 47 / 60 := by
  have h65 : (8.05 : ℝ) < Real.sqrt 65 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hin : Real.sqrt (37 - 3 * Real.sqrt 65) < 3.6 := by
    rw [Real.sqrt_lt' (by norm_num)]; nlinarith
  unfold s3; nlinarith

lemma core (h s : ℝ) (hh : 0 < h) (hs1 : 47 / 60 < s) (hs2 : s < 5 / 6) :
    0 < invStar 1 s ∧ invStar 1 s ≤ 2 * (5 / 6 - s) ∧ h11 1 s < 1 / 4 ∧
    (20 * (5 / 6 - s) < 1 - 4 * h → h < h11 1 s) ∧
    (64 * (h + 1) * (5 / 6 - s) < 1 → h < h10 1 s) := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 5 / 6 - s := ⟨_, rfl⟩
  rw [← hd]
  have hd0 : 0 < d := by linarith
  have hd1 : d < 1 / 20 := by linarith
  have harg : 0 ≤ 4 * 1 * s - 1 ^ 2 - 3 * s ^ 2 := by nlinarith
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = xRoot 1 s := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hxdef]; exact Real.sqrt_nonneg _
  have hx2 : x ^ 2 = 4 * 1 * s - 1 ^ 2 - 3 * s ^ 2 := by
    rw [hxdef]; exact Real.sq_sqrt harg
  have hxlo : 1 / 2 ≤ x := by nlinarith
  have hxhi : x ≤ 1 / 2 + d := by nlinarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 - 3 * s + x := ⟨_, rfl⟩
  have ht_lo : 3 * d ≤ t := by linarith
  have ht_hi : t ≤ 4 * d := by linarith
  have ht0 : 0 < t := by linarith
  have hinner : Real.sqrt (3 * 1 ^ 2 + 6 * s ^ 2 - 8 * 1 * s + (4 * 1 - 6 * s) * x) = t := by
    rw [show (3 * 1 ^ 2 + 6 * s ^ 2 - 8 * 1 * s + (4 * 1 - 6 * s) * x : ℝ) = t ^ 2 by
      rw [ht]; linear_combination (-1 : ℝ) * hx2]
    exact Real.sqrt_sq ht0.le
  have h17lo : (4 : ℝ) < Real.sqrt 17 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h17hi : Real.sqrt 17 < 5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hh11 : h11 1 s = (1 - Real.sqrt 17 * t) / 4 := by
    unfold h11; rw [← hxdef, hinner]
  have hinv : invStar 1 s = t / 2 := by
    unfold invStar; rw [← hxdef, ht]; ring
  have hw : -1 ≤ wDisc 1 s := by
    unfold wDisc; rw [← hxdef]; nlinarith [mul_nonneg hd0.le (by linarith : (0:ℝ) ≤ x - 1 / 2)]
  have hsw : Real.sqrt (-wDisc 1 s) ≤ 1 := by
    have := Real.sqrt_le_sqrt (show -wDisc 1 s ≤ 1 by linarith)
    rwa [Real.sqrt_one] at this
  refine ⟨by rw [hinv]; linarith, by rw [hinv]; linarith, ?_, ?_, ?_⟩
  · rw [hh11]; nlinarith
  · intro hcase
    rw [hh11]; nlinarith
  · intro hcase
    have hN : 8 * (1 - s) ^ 2 - 4 * 1 ^ 2 + 3 * (1 - 3 * s + x) ^ 2 ≤ -1 / 2 := by
      nlinarith
    have hden : (8 * (3 * s - 2 * 1 - x) : ℝ) = -(8 * t) := by rw [ht]; ring
    have hq : h + 1 < -(8 * (1 - s) ^ 2 - 4 * 1 ^ 2 + 3 * (1 - 3 * s + x) ^ 2) / (8 * t) := by
      rw [lt_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left ht_hi (by linarith : (0:ℝ) ≤ h + 1)
      nlinarith
    unfold h10 h7
    rw [← hxdef, hden, div_neg]
    rw [neg_div] at hq
    linarith

end SI1

/-- SI-1: which region table applies just below `s = 5/6` (α = 1). -/
theorem thresholds_near_five_sixths (h : ℝ) (hh : 0 < h) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Set.Ioo (5 / 6 - ε) (5 / 6),
      s3 1 ≤ s ∧
        ((h < h11 1 s ∧ h < 1 / 4) ∨
          (h11 1 s < h ∧ h < h10 1 s ∧ 0 < invStar 1 s ∧ h * invStar 1 s < 11 / 72)) := by
  by_cases hq : h < 1 / 4
  · refine ⟨min (1 / 20) ((1 - 4 * h) / 20), lt_min (by norm_num) (by linarith), ?_⟩
    rintro s ⟨hs1, hs2⟩
    have m1 := min_le_left (1 / 20 : ℝ) ((1 - 4 * h) / 20)
    have m2 := min_le_right (1 / 20 : ℝ) ((1 - 4 * h) / 20)
    obtain ⟨-, -, -, H8, -⟩ := SI1.core h s hh (by linarith) hs2
    exact ⟨by linarith [SI1.s3_lt], Or.inl ⟨H8 (by linarith), hq⟩⟩
  · replace hq : 1 / 4 ≤ h := not_lt.mp hq
    refine ⟨min (1 / 20) (1 / (64 * (h + 1))),
      lt_min (by norm_num) (by positivity), ?_⟩
    rintro s ⟨hs1, hs2⟩
    have m1 := min_le_left (1 / 20 : ℝ) (1 / (64 * (h + 1)))
    have m2 := min_le_right (1 / 20 : ℝ) (1 / (64 * (h + 1)))
    have hd : 5 / 6 - s < 1 / (64 * (h + 1)) := by linarith
    have hd' : 64 * (h + 1) * (5 / 6 - s) < 1 := by
      rw [lt_div_iff₀ (by positivity)] at hd; linarith
    obtain ⟨Hpos, Hle, H11, -, H10⟩ := SI1.core h s hh (by linarith) hs2
    refine ⟨by linarith [SI1.s3_lt], Or.inr ⟨by linarith, H10 hd', Hpos, ?_⟩⟩
    have : h * invStar 1 s ≤ h * (2 * (5 / 6 - s)) := mul_le_mul_of_nonneg_left Hle hh.le
    nlinarith


end StrategicInventory.Sequential

open StrategicInventory.Sequential in
theorem solution :
    ∀ h : ℝ, 0 < h → ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Set.Ioo (5 / 6 - ε) (5 / 6),
      (∃ σ : Profile, IsSPE 1 h s σ) ∧
        ∀ σ : Profile, IsSPE 1 h s σ →
          0 < σ.path.inventory ∧ h * σ.path.inventory < 11 / 72 := by
  intro h hh
  obtain ⟨ε, hε, H⟩ := thresholds_near_five_sixths h hh
  refine ⟨min ε (1 / 12), lt_min hε (by norm_num), fun s hs => ?_⟩
  have hs' : s ∈ Set.Ioo (5 / 6 - ε) (5 / 6) :=
    ⟨lt_of_le_of_lt (by linarith [min_le_left ε (1 / 12)]) hs.1, hs.2⟩
  have hs0 : 0 ≤ s := by linarith [hs.1, min_le_right ε (1 / 12)]
  obtain ⟨hs3, hcase⟩ := H s hs'
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · obtain ⟨hex, hall⟩ := region8_path 1 h s one_pos hh.le hs0
      (Or.inl ⟨h1, hs3, by linarith [hs.2]⟩)
    refine ⟨hex, fun σ hσ => ?_⟩
    rw [hall σ hσ]
    simp only [Outcome.inventory]
    constructor <;> nlinarith
  · obtain ⟨hex, hall⟩ := region7_path 1 h s one_pos hh.le hs0
      ⟨h1, h2, hs3, by linarith [hs.2]⟩
    refine ⟨hex, fun σ hσ => ?_⟩
    rw [hall σ hσ]
    simp only [Outcome.inventory]
    constructor <;> nlinarith
