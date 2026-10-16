-- Prove2me | solution 1 for SecondLawThermo.thermodynamic_temperature
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T23:17:03.751873+00:00
-- url     : https://prove2.me/submissions/b5b5035d-973c-432d-a8f3-1587f8c6238e

import Definitions.Def_SecondLawThermo_Defs
import Mathlib
import Theorems.Thm_SecondLawThermo_same_reservoir_ratio
import Theorems.Thm_SecondLawThermo_carnot_ratio_mul
import Theorems.Thm_SecondLawThermo_temperature_unique
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open SecondLawThermo
theorem solution {Θ : Type*} [LinearOrder Θ] (𝒞 : Set (SecondLawThermo.Cycle Θ))
    (h𝒞 : IsCycleCone 𝒞) (hCl : ClausiusStatement 𝒞) (hCarnot : CarnotEnginesExist 𝒞)
    (T₀ : Θ) :
    ∃ T : Θ → ℝ, (∀ t, 0 < T t) ∧ T T₀ = 273.16 ∧
      (∀ (h k : Θ) (e : SecondLawThermo.Cycle Θ), k < h → IsCarnotEngine 𝒞 e h k →
        |e k| / |e h| = T k / T h) ∧
      ∀ T' : Θ → ℝ, (∀ t, 0 < T' t) → T' T₀ = 273.16 →
        (∀ (h k : Θ) (e : SecondLawThermo.Cycle Θ), k < h → IsCarnotEngine 𝒞 e h k →
          |e k| / |e h| = T' k / T' h) → T' = T := by
  classical
  let R : Θ → ℝ := fun t =>
    if hlt : t < T₀ then 273.16 * ((-(hCarnot T₀ t hlt).choose t) / ((hCarnot T₀ t hlt).choose T₀))
    else if hgt : T₀ < t then 273.16 / ((-(hCarnot t T₀ hgt).choose T₀) / ((hCarnot t T₀ hgt).choose t))
    else 273.16
  have h273 : (273.16 : ℝ) ≠ 0 := by norm_num
  have hRpos : ∀ t, 0 < R t := by
    intro t
    by_cases hlt : t < T₀
    · simp only [R, dif_pos hlt]
      have he := (hCarnot T₀ t hlt).choose_spec
      rcases he with ⟨⟨hmem, hmemneg⟩, hbetween, hhot, hcold, hwork⟩
      exact mul_pos (by norm_num) (div_pos (neg_pos.mpr hcold) hhot)
    · by_cases hgt : T₀ < t
      · simp only [R, dif_neg hlt, dif_pos hgt]
        have he := (hCarnot t T₀ hgt).choose_spec
        rcases he with ⟨⟨hmem, hmemneg⟩, hbetween, hhot, hcold, hwork⟩
        exact div_pos (by norm_num) (div_pos (neg_pos.mpr hcold) hhot)
      · simp only [R, dif_neg hlt, dif_neg hgt]
        norm_num
  have hRT₀ : R T₀ = 273.16 := by simp [R]
  have hRcorrect : ∀ (h k : Θ) (e : SecondLawThermo.Cycle Θ), k < h → IsCarnotEngine 𝒞 e h k →
      |e k| / |e h| = R k / R h := by
    intro h k e hkh he
    by_cases hk0 : k = T₀
    · rw [hk0] at hkh he ⊢
      rw [hRT₀]
      have heh := (hCarnot h T₀ hkh).choose_spec
      have hS := SecondLawThermo.same_reservoir_ratio 𝒞 h𝒞 hCl h T₀ hkh e _ he heh
      rcases he with ⟨⟨hmeme, hmemnege⟩, hbetweene, hhote, hcolde, hworke⟩
      rcases heh with ⟨⟨hmemb, hmemnegb⟩, hbetweenb, hhotb, hcoldb, hworkb⟩
      simp only [R, dif_neg (not_lt.mpr (le_of_lt hkh)), dif_pos hkh]
      rw [abs_of_neg hcolde, abs_of_pos hhote] at ⊢
      rw [hS]
      field_simp [h273, ne_of_gt hhotb, ne_of_gt (neg_pos.mpr hcoldb), div_ne_zero (ne_of_gt (neg_pos.mpr hcoldb)) (ne_of_gt hhotb), div_ne_zero h273 (div_ne_zero (ne_of_gt (neg_pos.mpr hcoldb)) (ne_of_gt hhotb))] <;> ring
    · by_cases hh0 : h = T₀
      · rw [hh0] at hkh he ⊢
        rw [hRT₀]
        have hea := (hCarnot T₀ k hkh).choose_spec
        have hS := SecondLawThermo.same_reservoir_ratio 𝒞 h𝒞 hCl T₀ k hkh _ e hea he
        rcases he with ⟨⟨hmeme, hmemnege⟩, hbetweene, hhote, hcolde, hworke⟩
        rcases hea with ⟨⟨hmema, hmemnega⟩, hbetweena, hhota, hcolda, hworka⟩
        simp only [R, dif_pos hkh]
        rw [abs_of_neg hcolde, abs_of_pos hhote] at ⊢
        rw [← hS]
        field_simp [h273, ne_of_gt hhote, ne_of_gt (neg_pos.mpr hcolde), ne_of_gt hhota, ne_of_gt (neg_pos.mpr hcolda), div_ne_zero (ne_of_gt (neg_pos.mpr hcolda)) (ne_of_gt hhota), div_ne_zero h273 (div_ne_zero (ne_of_gt (neg_pos.mpr hcolda)) (ne_of_gt hhota))] <;> ring
      · have hkT : k < T₀ ∨ T₀ < k := lt_or_gt_of_ne hk0
        have hhT : h < T₀ ∨ T₀ < h := lt_or_gt_of_ne hh0
        rcases hkT with hkT | hkT
        · rcases hhT with hhT | hhT
          · -- k < h < T₀: triple (T₀, h, k)
            have hea := (hCarnot T₀ k (lt_trans hkh hhT)).choose_spec
            have heb := (hCarnot T₀ h hhT).choose_spec
            have hC := SecondLawThermo.carnot_ratio_mul 𝒞 h𝒞 hCl T₀ h k hkh hhT _ _ _ hea heb he
            rcases hea with ⟨⟨hmema, hmemnega⟩, hbetweena, hhota, hcolda, hworka⟩
            rcases heb with ⟨⟨hmemb, hmemnegb⟩, hbetweenb, hhotb, hcoldb, hworkb⟩
            rcases he with ⟨⟨hmeme, hmemnege⟩, hbetweene, hhote, hcolde, hworke⟩
            have hE : |e k| / |e h| = ((|(hCarnot T₀ k (lt_trans hkh hhT)).choose k| / |(hCarnot T₀ k (lt_trans hkh hhT)).choose T₀|) / ((|(hCarnot T₀ h hhT).choose h| / |(hCarnot T₀ h hhT).choose T₀|))) := by
              rw [hC]
              rw [abs_of_neg hcolde, abs_of_pos hhote, abs_of_neg hcoldb, abs_of_pos hhotb]
              field_simp [ne_of_gt (neg_pos.mpr hcolde), ne_of_lt hcolde, ne_of_gt hhote, ne_of_gt (neg_pos.mpr hcoldb), ne_of_lt hcoldb, ne_of_gt hhotb, div_ne_zero (ne_of_gt (neg_pos.mpr hcoldb)) (ne_of_gt hhotb), div_ne_zero (ne_of_lt hcoldb) (ne_of_gt hhotb), div_ne_zero (ne_of_lt hcolde) (ne_of_gt hhote)] <;> ring
            simp only [R, dif_pos (lt_trans hkh hhT), dif_pos hhT]
            rw [hE]
            rw [abs_of_neg hcolda, abs_of_pos hhota, abs_of_neg hcoldb, abs_of_pos hhotb]
            field_simp [h273, ne_of_gt (neg_pos.mpr hcolda), ne_of_gt hhota, ne_of_gt (neg_pos.mpr hcoldb), ne_of_gt hhotb, div_ne_zero (ne_of_gt (neg_pos.mpr hcolda)) (ne_of_gt hhota), div_ne_zero (ne_of_gt (neg_pos.mpr hcoldb)) (ne_of_gt hhotb), div_ne_zero h273 (div_ne_zero (ne_of_gt (neg_pos.mpr hcolda)) (ne_of_gt hhota)), div_ne_zero h273 (div_ne_zero (ne_of_gt (neg_pos.mpr hcoldb)) (ne_of_gt hhotb))] <;> ring
          · -- k < T₀ < h: triple (h, T₀, k)
            have hea := (hCarnot T₀ k hkT).choose_spec
            have heb := (hCarnot h T₀ hhT).choose_spec
            have hC := SecondLawThermo.carnot_ratio_mul 𝒞 h𝒞 hCl h T₀ k hkT hhT e _ _ he heb hea
            simp only [R, dif_pos hkT, dif_neg (not_lt.mpr (le_of_lt hhT)), dif_pos hhT]
            rw [hC]
            rcases hea with ⟨⟨hmema, hmemnega⟩, hbetweena, hhota, hcolda, hworka⟩
            rcases heb with ⟨⟨hmemb, hmemnegb⟩, hbetweenb, hhotb, hcoldb, hworkb⟩
            rw [abs_of_neg hcolda, abs_of_pos hhota, abs_of_neg hcoldb, abs_of_pos hhotb]
            field_simp [h273, ne_of_gt (neg_pos.mpr hcolda), ne_of_gt hhota, ne_of_gt (neg_pos.mpr hcoldb), ne_of_gt hhotb, div_ne_zero (ne_of_gt (neg_pos.mpr hcolda)) (ne_of_gt hhota), div_ne_zero (ne_of_gt hhotb) (ne_of_gt (neg_pos.mpr hcoldb))] <;> ring
        · -- T₀ < k < h: triple (h, k, T₀)
          have hTh : T₀ < h := lt_trans hkT hkh
          have hea := (hCarnot k T₀ hkT).choose_spec
          have heb := (hCarnot h T₀ hTh).choose_spec
          have hC := SecondLawThermo.carnot_ratio_mul 𝒞 h𝒞 hCl h k T₀ hkT hkh _ _ _ heb he hea
          rcases hea with ⟨⟨hmema, hmemnega⟩, hbetweena, hhota, hcolda, hworka⟩
          rcases heb with ⟨⟨hmemb, hmemnegb⟩, hbetweenb, hhotb, hcoldb, hworkb⟩
          rcases he with ⟨⟨hmeme, hmemnege⟩, hbetweene, hhote, hcolde, hworke⟩
          have hE : |e k| / |e h| = ((|(hCarnot h T₀ hTh).choose T₀| / |(hCarnot h T₀ hTh).choose h|) / ((|(hCarnot k T₀ hkT).choose T₀| / |(hCarnot k T₀ hkT).choose k|))) := by
            rw [hC]
            rw [abs_of_neg hcolde, abs_of_pos hhote, abs_of_neg hcolda, abs_of_pos hhota]
            field_simp [h273, ne_of_gt (neg_pos.mpr hcolde), ne_of_lt hcolde, ne_of_gt hhote, ne_of_gt (neg_pos.mpr hcolda), ne_of_lt hcolda, ne_of_gt hhota, ne_of_gt (neg_pos.mpr hcoldb), ne_of_lt hcoldb, ne_of_gt hhotb, div_ne_zero (ne_of_gt (neg_pos.mpr hcolde)) (ne_of_gt hhote), div_ne_zero (ne_of_lt hcolde) (ne_of_gt hhote), div_ne_zero (ne_of_gt (neg_pos.mpr hcolda)) (ne_of_gt hhota), div_ne_zero (ne_of_lt hcolda) (ne_of_gt hhota)] <;> ring
          simp only [R, dif_neg (not_lt.mpr (le_of_lt hkT)), dif_pos hkT, dif_neg (not_lt.mpr (le_of_lt hTh)), dif_pos hTh]
          rw [hE]
          rw [abs_of_neg hcolda, abs_of_pos hhota, abs_of_neg hcoldb, abs_of_pos hhotb]
          field_simp [h273, ne_of_gt (neg_pos.mpr hcolda), ne_of_gt hhota, ne_of_gt (neg_pos.mpr hcoldb), ne_of_gt hhotb, div_ne_zero (ne_of_gt (neg_pos.mpr hcolda)) (ne_of_gt hhota), div_ne_zero (ne_of_gt hhotb) (ne_of_gt (neg_pos.mpr hcoldb)), div_ne_zero h273 (div_ne_zero (ne_of_gt (neg_pos.mpr hcolda)) (ne_of_gt hhota)), div_ne_zero h273 (div_ne_zero (ne_of_gt hhotb) (ne_of_gt (neg_pos.mpr hcoldb)))] <;> ring
  refine ⟨R, hRpos, hRT₀, hRcorrect, ?_⟩
  intro T' hT'pos hT'₀ hT'corr
  exact SecondLawThermo.temperature_unique 𝒞 hCarnot T₀ R T' hRpos hRT₀ hRcorrect hT'pos hT'₀ hT'corr
