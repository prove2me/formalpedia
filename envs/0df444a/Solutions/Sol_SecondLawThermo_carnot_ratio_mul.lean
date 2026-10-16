-- Prove2me | solution 1 for SecondLawThermo.carnot_ratio_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T21:10:42.775348+00:00
-- url     : https://prove2.me/submissions/776be6cd-c3f4-4d36-86cf-eec72fb489b9

import Definitions.Def_SecondLawThermo_Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_SecondLawThermo_work_two_reservoirs
import Theorems.Thm_SecondLawThermo_same_reservoir_ratio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SecondLawThermo

theorem solution {Θ : Type*} [LinearOrder Θ] (𝒞 : Set (SecondLawThermo.Cycle Θ))
    (h𝒞 : IsCycleCone 𝒞) (hCl : ClausiusStatement 𝒞) (T₁ T₂ T₃ : Θ)
    (h₃₂ : T₃ < T₂) (h₂₁ : T₂ < T₁) (e₁ e₂ e₃ : SecondLawThermo.Cycle Θ)
    (he₁ : IsCarnotEngine 𝒞 e₁ T₁ T₃) (he₂ : IsCarnotEngine 𝒞 e₂ T₁ T₂)
    (he₃ : IsCarnotEngine 𝒞 e₃ T₂ T₃) :
    |e₁ T₃| / |e₁ T₁| = (|e₂ T₂| / |e₂ T₁|) * (|e₃ T₃| / |e₃ T₂|) := by
  classical
  rcases he₁ with ⟨hrev₁, hbetween₁, hhot₁, hcold₁, hwork₁⟩
  rcases he₂ with ⟨hrev₂, hbetween₂, hhot₂, hcold₂, hwork₂⟩
  rcases he₃ with ⟨hrev₃, hbetween₃, hhot₃, hcold₃, hwork₃⟩
  rcases hrev₁ with ⟨hmem₁, hmem₁neg⟩
  rcases hrev₂ with ⟨hmem₂, hmem₂neg⟩
  rcases hrev₃ with ⟨hmem₃, hmem₃neg⟩
  have h₁hot : 0 < e₁ T₁ := hhot₁
  have h₁cold : e₁ T₃ < 0 := hcold₁
  have h₂hot : 0 < e₂ T₁ := hhot₂
  have h₂cold : e₂ T₂ < 0 := hcold₂
  have h₃hot : 0 < e₃ T₂ := hhot₃
  have h₃cold : e₃ T₃ < 0 := hcold₃
  have h₁ : |e₁ T₁| = e₁ T₁ := abs_of_pos h₁hot
  have h₂ : |e₂ T₁| = e₂ T₁ := abs_of_pos h₂hot
  have h₃ : |e₂ T₂| = -e₂ T₂ := abs_of_neg h₂cold
  have h₄ : |e₃ T₂| = e₃ T₂ := abs_of_pos h₃hot
  have h₅ : |e₃ T₃| = -e₃ T₃ := abs_of_neg h₃cold
  have h₆ : |e₁ T₃| = -e₁ T₃ := abs_of_neg h₁cold
  have h31 : T₃ < T₁ := lt_trans h₃₂ h₂₁
  have hT1_ne_T2 : T₁ ≠ T₂ := ne_of_gt h₂₁
  have hT1_ne_T3 : T₁ ≠ T₃ := ne_of_gt h31
  have hT3_ne_T1 : T₃ ≠ T₁ := ne_of_lt h31
  have hT3_ne_T2 : T₃ ≠ T₂ := ne_of_lt h₃₂
  have hT2_ne_T1 : T₂ ≠ T₁ := ne_of_lt h₂₁
  have h3T1 : e₃ T₁ = 0 := hbetween₃ T₁ hT1_ne_T2 hT1_ne_T3
  have h2T3 : e₂ T₃ = 0 := hbetween₂ T₃ hT3_ne_T1 hT3_ne_T2
  let scale : ℝ := (-e₂ T₂) / e₃ T₂
  have hscale : 0 < scale := div_pos (neg_pos.mpr h₂cold) h₃hot
  have hmid : e₂ T₂ + scale * e₃ T₂ = 0 := by
    dsimp [scale]
    field_simp [ne_of_gt h₃hot]
    ring
  let composite : SecondLawThermo.Cycle Θ := e₂ + scale • e₃
  have hcompbetween : OperatesBetween composite T₁ T₃ := by
    intro t ht1 ht3
    by_cases ht2 : t = T₂
    · subst t
      simpa [composite] using hmid
    · have hz2 := hbetween₂ t ht1 ht2
      have hz3 := hbetween₃ t ht2 ht3
      simp [composite, hz2, hz3]
  have hcompmem : composite ∈ 𝒞 := by
    apply h𝒞.add_mem
    · exact hmem₂
    · exact h𝒞.smul_mem scale e₃ hscale.le hmem₃
  have hcompnegmem : -composite ∈ 𝒞 := by
    have heq : -composite = (-e₂) + scale • (-e₃) := by
      ext t
      simp [composite] <;> ring
    rw [heq]
    exact h𝒞.add_mem (-e₂) (scale • (-e₃)) hmem₂neg (h𝒞.smul_mem scale (-e₃) hscale.le hmem₃neg)
  have hcomp_hot : 0 < composite T₁ := by
    simpa [composite, h3T1] using h₂hot
  have hcomp_cold : composite T₃ < 0 := by
    rw [show composite T₃ = scale * e₃ T₃ by simp [composite, h2T3]]
    exact mul_neg_of_pos_of_neg hscale h₃cold
  have hcompwork : work composite = work e₂ + scale * work e₃ := by
    rw [work_two_reservoirs composite T₁ T₃ h31 hcompbetween]
    rw [work_two_reservoirs e₂ T₁ T₂ h₂₁ hbetween₂]
    rw [work_two_reservoirs e₃ T₂ T₃ h₃₂ hbetween₃]
    simp [composite, h3T1, h2T3]
    nlinarith [hmid]
  have hcomp_work : 0 < work composite := by
    rw [hcompwork]
    nlinarith [hwork₂, hwork₃, hscale]
  have hengine₁ : IsCarnotEngine 𝒞 e₁ T₁ T₃ :=
    ⟨⟨hmem₁, hmem₁neg⟩, hbetween₁, h₁hot, h₁cold, hwork₁⟩
  have hengine_comp : IsCarnotEngine 𝒞 composite T₁ T₃ :=
    ⟨⟨hcompmem, hcompnegmem⟩, hcompbetween, hcomp_hot, hcomp_cold, hcomp_work⟩
  have hratio :=
    same_reservoir_ratio 𝒞 h𝒞 hCl T₁ T₃ h31 e₁ composite hengine₁ hengine_comp
  have hcomposite_ratio :
      (-composite T₃) / composite T₁ =
        ((-e₂ T₂) / e₂ T₁) * ((-e₃ T₃) / e₃ T₂) := by
    dsimp [composite, scale]
    rw [h2T3, h3T1]
    field_simp [ne_of_gt h₂hot, ne_of_gt h₃hot]
    ring
  rw [h₁, h₂, h₃, h₄, h₅, h₆]
  rw [hratio, hcomposite_ratio]
