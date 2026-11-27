-- Prove2me | solution 1 for OpaquePricing.Dominance.Supplement.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:21:40.41732+00:00
-- url     : https://prove2.me/submissions/933fb528-61d4-41a1-a32e-1eca84f1f359

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_Optimization

open MeasureTheory

open OpaquePricing
open OpaquePricing.Dominance
open OpaquePricing.Dominance.Supplement

theorem solution {N : ℕ} (hN : 2 ≤ N) :
    (∃ z : RatioPoint N, 0 < ratioDen z ∧
      ENNReal.ofReal (ratioValue z) = optRatio N) ∧
    optRatio N ≤ ENNReal.ofReal (2 - 1 / (N : ℝ)) := by
      have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
      have ht0 : 0 ≤ 1 / (N : ℝ) := by positivity
      have ht1 : 1 / (N : ℝ) ≤ 1 := by
        rw [div_le_one hNpos]; linarith
      have hub : optRatio N ≤ ENNReal.ofReal (2 - 1 / (N : ℝ)) := by
        unfold optRatio
        refine iSup₂_le fun z hz => ?_
        apply ENNReal.ofReal_le_ofReal
        unfold ratioValue
        rw [div_le_iff₀ hz]
        have h1 : z.x * (z.a + z.b) ≤ ratioDen z := le_max_left _ _
        have h2 : z.y * (z.a + z.b + z.c) ≤ ratioDen z := le_max_right _ _
        have hx : 0 ≤ z.x := by
          have := z.x_nonneg
          rw [le_div_iff₀ hNpos] at this; linarith
        have hy : z.x * (1 / (N : ℝ)) ≤ z.y := by
          have := z.lower
          rw [div_eq_mul_one_div] at this; exact this
        have ha := z.a_nonneg
        have hb := z.b_nonneg
        nlinarith [mul_nonneg ha (sub_nonneg.mpr hy),
          mul_nonneg (sub_nonneg.mpr ht1) (mul_nonneg hx hb),
          mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h1)]
      let z0 : RatioPoint N :=
        { x := N, y := 1, a := 1 / N, b := 0, c := ((N : ℝ) - 1) / N, d := 0
          a_nonneg := ht0
          b_nonneg := le_refl 0
          c_nonneg := by apply div_nonneg <;> linarith
          d_nonneg := le_refl 0
          total := by field_simp; ring
          y_le_x := by linarith
          lower := by rw [div_self hNne]
          x_nonneg := by rw [div_self hNne]; norm_num }
      have hden : ratioDen z0 = 1 := by
        unfold ratioDen
        simp only [z0]
        have e1 : (N : ℝ) * (1 / N + 0) = 1 := by rw [add_zero]; field_simp
        have e2 : (1 : ℝ) * (1 / N + 0 + ((N : ℝ) - 1) / N) = 1 := by field_simp; ring
        rw [e1, e2, max_self]
      have hval : ratioValue z0 = 2 - 1 / (N : ℝ) := by
        unfold ratioValue
        rw [hden, div_one]
        simp only [z0]
        field_simp; ring
      have hlb : ENNReal.ofReal (ratioValue z0) ≤ optRatio N := by
        unfold optRatio
        exact le_iSup₂ (f := fun (z : RatioPoint N) (_ : 0 < ratioDen z) => ENNReal.ofReal (ratioValue z))
          z0 (by rw [hden]; norm_num)
      refine ⟨⟨z0, by rw [hden]; norm_num, le_antisymm hlb ?_⟩, hub⟩
      rw [hval]; exact hub
