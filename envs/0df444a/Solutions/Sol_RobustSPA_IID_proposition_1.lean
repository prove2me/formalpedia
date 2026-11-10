-- Prove2me | solution 1 for RobustSPA.IID.proposition_1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T17:57:53.657221+00:00
-- url     : https://prove2.me/submissions/e84d203a-0f1c-4924-8557-36d5e874c63f

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting

open MeasureTheory Set RobustSPA.IID
open scoped Classical

namespace Prop1Disproof

noncomputable def φ0 : ℝ → ℝ := (Set.Icc (0 : ℝ) 1).indicator (fun _ => 1)

lemma φ0_meas : Measurable φ0 := measurable_const.indicator measurableSet_Icc

lemma φ0_nonneg (v : ℝ) : 0 ≤ φ0 v := by
  unfold φ0
  by_cases hv : v ∈ Set.Icc (0 : ℝ) 1 <;> simp [hv]

lemma φ0_supp (v : ℝ) (hv : v ∉ Set.Icc (0 : ℝ) 1) : φ0 v = 0 :=
  Set.indicator_of_notMem hv _

noncomputable def ρ0_meas : Measure ℝ :=
  volume.withDensity (fun v => ENNReal.ofReal (φ0 v))

lemma ρ0_eq_restrict : ρ0_meas = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  unfold ρ0_meas φ0
  have h1 : (fun v : ℝ => ENNReal.ofReal ((Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) v)) =
      (Set.Icc (0 : ℝ) 1).indicator (1 : ℝ → ENNReal) := by
    ext v
    by_cases hv : v ∈ Set.Icc (0 : ℝ) 1 <;> simp [hv]
  rw [h1, withDensity_indicator measurableSet_Icc, withDensity_one]

instance : IsProbabilityMeasure ρ0_meas := by
  rw [ρ0_eq_restrict]
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

noncomputable def ρ0 : ProbabilityMeasure ℝ := ⟨ρ0_meas, inferInstance⟩

def v1 : Fin 1 → ℝ := fun _ => 1

lemma v1_mem_cube : v1 ∈ cube 1 := fun _ _ => ⟨zero_le_one, le_rfl⟩

lemma μ1_mem_Fall : (Measure.dirac v1 : Measure (Fin 1 → ℝ)) ∈ Fall 1 := by
  refine ⟨inferInstance, ?_⟩
  have hnot : v1 ∉ (cube 1)ᶜ := by simp [v1_mem_cube]
  simp [Set.indicator, hnot]

lemma top_v1 : top v1 = 1 := by
  unfold top v1
  exact ciSup_const

lemma second_v1 : second v1 = 0 := by
  have he : IsEmpty {q : Fin 1 × Fin 1 // q.1 ≠ q.2} :=
    ⟨fun ⟨⟨a, b⟩, h⟩ => h (Subsingleton.elim a b)⟩
  unfold second
  exact @Real.iSup_of_isEmpty {q : Fin 1 × Fin 1 // q.1 ≠ q.2} he _

lemma win_v1 : isWinner v1 0 :=
  ⟨fun _ => le_rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩

lemma spa_p0 : (SPA (n := 1) (ρ0 : Measure ℝ)).p 0 v1 = 1 / 2 := by
  unfold SPA
  dsimp only
  rw [if_pos win_v1, second_v1]
  change ∫ q, (Set.Iic (v1 0)).indicator (fun q => max (0 : ℝ) q) q ∂ρ0_meas = 1 / 2
  rw [ρ0_eq_restrict]
  have hcongr : ∀ q ∈ Set.Icc (0 : ℝ) 1,
      (Set.Iic (v1 0)).indicator (fun q => max (0 : ℝ) q) q = q := by
    intro q hq
    have hq1 : q ∈ Set.Iic (v1 0) := hq.2
    rw [Set.indicator_of_mem hq1, max_eq_right hq.1]
  rw [setIntegral_congr_fun measurableSet_Icc hcongr, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, integral_id]
  norm_num

lemma regret_eq_half : regret (SPA (ρ0 : Measure ℝ)) (Measure.dirac v1) = 1 / 2 := by
  unfold regret
  rw [integral_dirac, Fin.sum_univ_one, top_v1, spa_p0]
  norm_num

end Prop1Disproof

open Prop1Disproof in
theorem solution : ¬ (∀ (n : ℕ) (_hn : 0 < n) (r : ℝ) (_hr : r ∈ Set.Icc (0 : ℝ) 1)
    (φ : ℝ → ℝ) (_hφm : Measurable φ) (_hφ0 : ∀ v, 0 ≤ φ v)
    (_hφs : ∀ v ∉ Set.Icc r 1, φ v = 0)
    (ρ : ProbabilityMeasure ℝ)
    (_hρ : (ρ : Measure ℝ) = volume.withDensity (fun v => ENNReal.ofReal (φ v))),
    (∀ μ ∈ Fall n, regret (SPA (ρ : Measure ℝ)) μ =
      r - ∫ v in (0 : ℝ)..r, F1 μ v +
        ∫ v in r..1, ((1 - v * φ v - cdfOf ρ v) * (1 - F1 μ v) +
          cdfOf ρ v * (F2 μ v - F1 μ v))) ∧
    (∀ G : ProbabilityMeasure ℝ, (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0 →
      regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ)) =
        r - ∫ v in (0 : ℝ)..r, (cdfOf G v) ^ n +
          ∫ v in r..1, ((1 - v * φ v - cdfOf ρ v) * (1 - (cdfOf G v) ^ n) +
            cdfOf ρ v * n * (cdfOf G v) ^ (n - 1) * (1 - cdfOf G v)))) := by
  intro H
  have hr : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h := (H 1 one_pos 0 hr φ0 φ0_meas φ0_nonneg φ0_supp ρ0 rfl).1
    (Measure.dirac v1) μ1_mem_Fall
  rw [regret_eq_half, intervalIntegral.integral_same] at h
  norm_num at h
