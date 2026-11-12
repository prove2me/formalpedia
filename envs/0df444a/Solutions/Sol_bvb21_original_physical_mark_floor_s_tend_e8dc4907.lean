-- Prove2me | solution 1 for bvb21_original_physical_mark_floor_s_tend_e8dc4907
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:45:17.223068+00:00
-- url     : https://prove2.me/submissions/77cef159-75d0-4762-bc8f-8721241ce294

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_discounted_mark_rate_left_continuous_on_cap
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hpre : (t : ℝ≥0∞) < ruinTime X x D ω)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q T : ℝ) (hT : 0 < T) 
    (hn : (let v : ℕ → ℝ := (fun n => T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2)); let s : ℕ → ℝ≥0 := fun n => Real.toNNReal (v n); (∀ (n : ℕ), 0 ≤ v n)))
    (hs_le : (let v : ℕ → ℝ := (fun n => T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2)); let s : ℕ → ℝ≥0 := fun n => Real.toNNReal (v n); (∀ (n : ℕ), s n ≤ t)))
    : (let v : ℕ → ℝ := (fun n => T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2)); let s : ℕ → ℝ≥0 := fun n => Real.toNNReal (v n); Tendsto s atTop (𝓝 t)) := by
    let v : ℕ → ℝ := fun n => T *
        (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2)
    let s : ℕ → ℝ≥0 := fun n => Real.toNNReal (v n)
    have hfloor := avram_bvb_b21_original_uniform_floor_samples_converge_from_left
        T (t : ℝ) hT t.property
    have hc := (continuous_real_toNNReal.tendsto (t : ℝ)).comp hfloor.2
    rw [Real.toNNReal_coe] at hc
    change Tendsto (Real.toNNReal ∘ v) atTop (𝓝 t)
    exact hc
end
