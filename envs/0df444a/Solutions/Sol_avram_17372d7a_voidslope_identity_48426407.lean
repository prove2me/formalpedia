-- Prove2me | solution 1 for avram_17372d7a_voidslope_identity_48426407
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:08:55.056347+00:00
-- url     : https://prove2.me/submissions/a8fe1d35-aba8-40dd-a511-e5761c3258cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_nonvoid_second_order_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_occupied_cell_probability
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_bonferroni_void_rate_squeeze_atTop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (hT : 0 < T) 
    (hJK : (let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1))); let J : ℝ≥0 → Ω → ℝ≥0∞ := (fun t ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B)); let K : ℝ≥0 → Ω → ℕ := (fun t ω => {u : ℝ≥0 | 0 < u ∧ u ≤ t ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -(1 / ((n : ℝ) + 1))}.ncard); (∀ (t : ℝ≥0) (ω : Ω), J t ω = (K t ω : ℝ≥0∞))))
    (hProb : (let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1))); let J : ℝ≥0 → Ω → ℝ≥0∞ := (fun t ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B)); let K : ℝ≥0 → Ω → ℕ := (fun t ω => {u : ℝ≥0 | 0 < u ∧ u ≤ t ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -(1 / ((n : ℝ) + 1))}.ncard); (∀ (t : ℝ≥0), 1 - (P {ω : Ω | J t ω = 0}).toReal =
        P.real {ω : Ω | K t ω ≠ 0})))
    : (let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1))); let J : ℝ≥0 → Ω → ℝ≥0∞ := (fun t ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B)); let K : ℝ≥0 → Ω → ℕ := (fun t ω => {u : ℝ≥0 | 0 < u ∧ u ≤ t ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -(1 / ((n : ℝ) + 1))}.ncard); let r : ℝ := (T : ℝ) * (X.ν B).toReal; let p : ℕ → ℝ := (fun k => 1 - (P {ω : Ω | J (T / (k : ℝ≥0)) ω = 0}).toReal); Filter.Tendsto (fun k : ℕ => (k : ℝ) * p k)
      Filter.atTop (nhds r)) := by
    classical
    letI : IsProbabilityMeasure P := X.isProbability
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let J : ℝ≥0 → Ω → ℝ≥0∞ := fun t ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ B)
    let K : ℝ≥0 → Ω → ℕ := fun t ω =>
        {u : ℝ≥0 | 0 < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ := (T : ℝ) * (X.ν B).toReal
    let p : ℕ → ℝ := fun k =>
        1 - (P {ω : Ω | J (T / (k : ℝ≥0)) ω = 0}).toReal
    apply avram_p4_f2_bonferroni_void_rate_squeeze_atTop r p
    intro k hk
    have hkPos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hRate :
        ((((T / (k : ℝ≥0)) : ℝ≥0∞) * X.ν B).toReal) =
          r / (k : ℝ) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_div]
      change ((T : ℝ) / (k : ℝ)) * (X.ν B).toReal =
        ((T : ℝ) * (X.ν B).toReal) / (k : ℝ)
      ring
    have hSource :=
      avram_p4_f2_original_negative_band_nonvoid_second_order_bound
        X (T / (k : ℝ≥0)) n
    dsimp only at hSource
    have hkNZ : (k : ℝ≥0) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hk)
    simp only [ENNReal.coe_div hkNZ] at hSource
    rw [hRate] at hSource
    have hp : p k = P.real {ω : Ω | K (T / (k : ℝ≥0)) ω ≠ 0} :=
      hProb (T / (k : ℝ≥0))
    rw [← hp] at hSource
    constructor
    · calc
        r - (r ^ 2 / 2) * (k : ℝ)⁻¹ =
          (k : ℝ) * (r / (k : ℝ) - (r / (k : ℝ)) ^ 2 / 2) := by
            field_simp
            <;> ring
        _ ≤ (k : ℝ) * p k :=
          mul_le_mul_of_nonneg_left hSource.1 hkPos.le
    · calc
        (k : ℝ) * p k ≤ (k : ℝ) * (r / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hSource.2 hkPos.le
        _ = r := by field_simp
