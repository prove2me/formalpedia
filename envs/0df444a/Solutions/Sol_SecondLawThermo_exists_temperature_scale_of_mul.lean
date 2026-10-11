-- Prove2me | solution 1 for SecondLawThermo.exists_temperature_scale_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:56:08.151274+00:00
-- url     : https://prove2.me/submissions/ac7f6068-f0b4-402d-ac8c-58a9b41ff480

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

open SecondLawThermo

theorem solution {Θ : Type*} [LinearOrder Θ] (f : Θ → Θ → ℝ)
    (hf_pos : ∀ h k : Θ, k < h → 0 < f h k)
    (hf_mul : ∀ T₁ T₂ T₃ : Θ, T₃ < T₂ → T₂ < T₁ → f T₁ T₃ = f T₁ T₂ * f T₂ T₃)
    (T₀ : Θ) (a : ℝ) (ha : 0 < a) :
    ∃ T : Θ → ℝ, (∀ t, 0 < T t) ∧ T T₀ = a ∧ ∀ h k : Θ, k < h → f h k = T k / T h := by
  let T : Θ → ℝ := fun t => if t < T₀ then a * f T₀ t else if t = T₀ then a else a / f t T₀
  refine ⟨T, ?_, ?_, ?_⟩
  · intro t
    rcases lt_trichotomy t T₀ with ht | rfl | ht
    · simpa [T, ht] using mul_pos ha (hf_pos T₀ t ht)
    · simpa [T] using ha
    · simpa [T, not_lt.mpr ht.le, ne_of_gt ht] using div_pos ha (hf_pos t T₀ ht)
  · simp [T]
  · intro h k hkh
    rcases lt_trichotomy h T₀ with hh | rfl | hh
    · have hk := hkh.trans hh
      have hm := hf_mul T₀ h k hkh hh
      have hn := (hf_pos T₀ h hh).ne'
      simp only [T, hh, hk, ↓reduceIte]
      field_simp
      nlinarith [hm]
    · simp [T, hkh, ha.ne']
    · rcases lt_trichotomy k T₀ with hk | rfl | hk
      · have hm := hf_mul h T₀ k hk hh
        have hn := (hf_pos h T₀ hh).ne'
        simp only [T, hk, not_lt.mpr hh.le, ne_of_gt hh, ↓reduceIte]
        field_simp
        nlinarith [hm]
      · simp [T, not_lt.mpr hh.le, ne_of_gt hh, ha.ne']
      · have hm := hf_mul h k T₀ hk hkh
        have hn := (hf_pos h T₀ hh).ne'
        have hn' := (hf_pos k T₀ hk).ne'
        simp only [T, not_lt.mpr hh.le, ne_of_gt hh, not_lt.mpr hk.le, ne_of_gt hk,
          ↓reduceIte]
        field_simp
        nlinarith [hm]
