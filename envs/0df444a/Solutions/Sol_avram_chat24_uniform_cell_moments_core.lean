-- Prove2me | solution 1 for avram_chat24_uniform_cell_moments_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:20:34.427142+00:00
-- url     : https://prove2.me/submissions/3bda9a13-faeb-466f-a4b9-3a9fce8948d1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_avram_chat24_right_path_measurable_core
import Theorems.Thm_avram_chat24_left_limit_measurable_core
import Theorems.Thm_avram_chat24_atomic_prefix_interval_core
import Theorems.Thm_avram_chat24_mapped_jump_cell_integral_core
import Theorems.Thm_avram_chat24_physical_cell_volume_core
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    (f : ℝ≥0 → ℝ) (d T : ℝ) (hT : 0 ≤ T)
    (B : ℝ≥0) (hB : 0 < B) (hBT : B ≤ (⟨T, hT⟩ : ℝ≥0))
    (hright : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hleft : ∀ t : ℝ≥0, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hdown : ∀ t : ℝ≥0, 0 < t → f t ≤ Function.leftLim f t)
    (hsum : Summable (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ B then Function.leftLim f t - f t else 0))
    (hsource : ∀ t : ℝ≥0, t ≤ B → f t = (t : ℝ) * d -
      ∑' r : ℝ≥0, if 0 < r ∧ r ≤ t then Function.leftLim f r - f r else 0) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ f t - Function.leftLim f t ≠ 0}).map
        (fun t : ℝ≥0 => (t, f t - Function.leftLim f t)))
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
    let m : ℕ → ℕ → ℝ := fun n i =>
      d * h n - (f (u n (i + 1)) - f (u n i))
    ∀ n : ℕ, 0 < h n ∧
      (∀ i ∈ Finset.range (n + 1),
        let H : ℝ≥0 × ℝ → ℝ := fun p =>
          if u n i < p.1 ∧ p.1 ≤ u n (i + 1) then -p.2 else 0
        Integrable H NX ∧ (∫ p, H p ∂NX) = m n i) ∧
      (∀ i ∈ Finset.range (n + 1),
        μ (Ioc (u n i) (u n (i + 1))) = ENNReal.ofReal (h n)) := by
  classical
  intro NX μ u h m
  have hΔ : Measurable (fun t => f t - Function.leftLim f t) :=
    (avram_chat24_right_path_measurable_core f hright).sub
      (avram_chat24_left_limit_measurable_core f hleft)
  have hstep (n i : ℕ) : (u n (i + 1) : ℝ) = (u n i : ℝ) + h n := by
    dsimp [u, h]
    push_cast
    ring
  have hub (n i : ℕ) (hi : i < n + 1) : u n (i + 1) ≤ B := by
    dsimp [u]
    apply (div_le_iff₀ (by positivity)).mpr
    gcongr
    exact_mod_cast (show i ≤ n from by omega)
  have huk (n i : ℕ) : u n i ≤ u n (i + 1) := by
    dsimp [u]
    gcongr
    exact_mod_cast (show i ≤ i + 1 from by omega)
  intro n
  refine ⟨div_pos (by exact_mod_cast hB) (by positivity), ?_, ?_⟩
  · intro i hi
    have hp := avram_chat24_atomic_prefix_interval_core f d B hsum hsource
      (u n i) (u n (i + 1)) (huk n i) (hub n i (Finset.mem_range.mp hi))
    have hsumΔ : Summable (fun t : ℝ≥0 =>
        if u n i < t ∧ t ≤ u n (i + 1) then -(f t - Function.leftLim f t) else 0) := by
      simpa only [neg_sub] using hp.1
    have hc := avram_chat24_mapped_jump_cell_integral_core
      (fun t => f t - Function.leftLim f t) hΔ
      (fun t ht => sub_nonpos.mpr (hdown t ht)) (u n i) (u n (i + 1)) hsumΔ
    refine ⟨hc.1, ?_⟩
    calc
      (∫ p : ℝ≥0 × ℝ, (if u n i < p.1 ∧ p.1 ≤ u n (i + 1) then -p.2 else 0) ∂NX) =
          ∑' t : ℝ≥0, if u n i < t ∧ t ≤ u n (i + 1) then
            -(f t - Function.leftLim f t) else 0 := hc.2
      _ = ∑' t : ℝ≥0, if u n i < t ∧ t ≤ u n (i + 1) then
            Function.leftLim f t - f t else 0 := by simp only [neg_sub]
      _ = m n i := by
        rw [hp.2]
        dsimp [m]
        rw [hstep]
        ring
  · intro i hi
    have htT : (u n (i + 1) : ℝ) ≤ T := by
      exact_mod_cast (hub n i (Finset.mem_range.mp hi)).trans hBT
    have hv := avram_chat24_physical_cell_volume_core T
      (u n i) (u n (i + 1)) (huk n i) htT
    simpa only [hstep, add_sub_cancel_left] using hv
end
