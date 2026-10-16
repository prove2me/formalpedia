-- Prove2me | solution 1 for SecondLawThermo.temperature_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T22:05:29.000877+00:00
-- url     : https://prove2.me/submissions/816f70cb-f03d-44c9-8945-4e3fbdb9bbfe

import Definitions.Def_SecondLawThermo_Defs
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SecondLawThermo

theorem solution {Θ : Type*} [LinearOrder Θ]
    (𝒞 : Set (SecondLawThermo.Cycle Θ)) (hCarnot : SecondLawThermo.CarnotEnginesExist 𝒞)
    (T₀ : Θ) (T T' : Θ → ℝ)
    (hTpos : ∀ t, 0 < T t) (hT₀ : T T₀ = 273.16)
    (hTcorr : ∀ (h k : Θ) (e : SecondLawThermo.Cycle Θ), k < h → SecondLawThermo.IsCarnotEngine 𝒞 e h k →
      |e k| / |e h| = T k / T h)
    (hT'pos : ∀ t, 0 < T' t) (hT'₀ : T' T₀ = 273.16)
    (hT'corr : ∀ (h k : Θ) (e : SecondLawThermo.Cycle Θ), k < h → SecondLawThermo.IsCarnotEngine 𝒞 e h k →
      |e k| / |e h| = T' k / T' h) :
    T' = T := by
  funext t
  by_cases ht : t = T₀
  · subst ht
    rw [hT'₀, hT₀]
  · rcases lt_or_gt_of_ne ht with hlt | hgt
    · obtain ⟨e, he⟩ := hCarnot T₀ t hlt
      have h1 := hTcorr T₀ t e hlt he
      have h2 := hT'corr T₀ t e hlt he
      have h273 : (273.16 : ℝ) ≠ 0 := by norm_num
      rw [hT₀] at h1
      rw [hT'₀] at h2
      exact ((mul_right_cancel₀ h273 ((div_eq_div_iff h273 h273).mp (h1.symm.trans h2)))).symm
    · obtain ⟨e, he⟩ := hCarnot t T₀ hgt
      have h1 := hTcorr t T₀ e hgt he
      have h2 := hT'corr t T₀ e hgt he
      have h273 : (273.16 : ℝ) ≠ 0 := by norm_num
      rw [hT₀] at h1
      rw [hT'₀] at h2
      exact mul_left_cancel₀ h273 ((div_eq_div_iff (ne_of_gt (hTpos t)) (ne_of_gt (hT'pos t))).mp (h1.symm.trans h2))
