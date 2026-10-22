-- Prove2me | solution 1 for UnknownLoads.Refined.lemma_21
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:55:54.66072+00:00
-- url     : https://prove2.me/submissions/68c42730-95c2-451e-98c6-27a21013ec8a

import Mathlib
import Definitions.Def_UnknownLoads_Refined_Load

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology UnknownLoads.Refined

theorem ul_cad_of_cont {f : ℝ → ℝ} (hf : Continuous f) (T : ℝ) : IsCadlagOn f T :=
  ⟨fun t _ => hf.continuousWithinAt, fun t _ => ⟨f t, (hf.tendsto t).mono_left nhdsWithin_le_nhds⟩⟩

theorem solution (T M ε : ℝ) (hM : 0 ≤ M) (x : ℝ → ℝ) (hx : LipSet T M ε x) :
    ∃ y : ℝ → ℝ, LipSet T M 0 y ∧ ∀ t ∈ Icc 0 T, |x t - y t| ≤ 4 * ε := by
  obtain ⟨hcad, hx0, hlip⟩ := hx
  by_cases hT : T < 0
  · refine ⟨fun _ => 0, ⟨ul_cad_of_cont continuous_const T, rfl, ?_⟩, ?_⟩
    · intro s hs; exact absurd (hs.1.trans hs.2) (not_le.mpr hT)
    · intro t ht; exact absurd (ht.1.trans ht.2) (not_le.mpr hT)
  push_neg at hT
  have hε : 0 ≤ ε := by
    have := hlip 0 ⟨le_refl _, hT⟩ 0 ⟨le_refl _, hT⟩
    simpa using this
  haveI : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_refl _, hT⟩⟩
  have hbdd : ∀ t : ℝ, BddBelow (Set.range fun s : Icc (0 : ℝ) T => x s + M * |t - s|) := by
    intro t
    refine ⟨-(M * T + ε), ?_⟩
    rintro v ⟨s, rfl⟩
    have h1 := hlip 0 ⟨le_refl _, hT⟩ s s.2
    have h2 := (abs_le.mp h1).1
    have h3 : 0 ≤ M * |t - s| := mul_nonneg hM (abs_nonneg _)
    have h4 : M * |(s : ℝ) - 0| ≤ M * T := by
      apply mul_le_mul_of_nonneg_left _ hM
      rw [sub_zero, abs_of_nonneg s.2.1]; exact s.2.2
    linarith
  set g : ℝ → ℝ := fun t => ⨅ s : Icc (0 : ℝ) T, (x s + M * |t - s|) with hg
  have hlow : ∀ t ∈ Icc (0 : ℝ) T, x t - ε ≤ g t := by
    intro t ht
    refine le_ciInf (fun s => ?_)
    have := (abs_le.mp (hlip s s.2 t ht)).2
    have h2 := (abs_le.mp (hlip s s.2 t ht)).1
    have h5 : |t - (s : ℝ)| = |(s : ℝ) - t| := abs_sub_comm _ _
    linarith
  have hup : ∀ t ∈ Icc (0 : ℝ) T, g t ≤ x t := by
    intro t ht
    have := ciInf_le (hbdd t) ⟨t, ht⟩
    simpa using this
  have hlipg : ∀ t t' : ℝ, g t ≤ g t' + M * |t - t'| := by
    intro t t'
    have : g t - M * |t - t'| ≤ g t' := by
      refine le_ciInf (fun s => ?_)
      have h1 : g t ≤ x s + M * |t - s| := ciInf_le (hbdd t) s
      have h2 : |t - (s : ℝ)| ≤ |t' - s| + |t - t'| := by
        calc |t - (s : ℝ)| = |(t' - s) + (t - t')| := by ring_nf
          _ ≤ |t' - s| + |t - t'| := abs_add_le _ _
      have h3 : M * |t - (s : ℝ)| ≤ M * (|t' - s| + |t - t'|) := mul_le_mul_of_nonneg_left h2 hM
      linarith
    linarith
  have hdist : ∀ t t' : ℝ, |g t - g t'| ≤ M * |t - t'| := by
    intro t t'
    rw [abs_le]
    have h1 := hlipg t t'
    have h2 := hlipg t' t
    rw [abs_sub_comm t' t] at h2
    constructor <;> linarith
  have hcont : Continuous g := by
    have : LipschitzWith M.toNNReal g := by
      refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hM]
      exact hdist a b
    exact this.continuous
  refine ⟨fun t => g t - g 0, ⟨ul_cad_of_cont (hcont.sub continuous_const) T, by simp, ?_⟩, ?_⟩
  · intro s _ t _
    have := hdist t s
    simp only [sub_sub_sub_cancel_right, add_zero]
    exact this
  · intro t ht
    have h1 := hlow t ht
    have h2 := hup t ht
    have h3 := hlow 0 ⟨le_refl _, hT⟩
    have h4 := hup 0 ⟨le_refl _, hT⟩
    rw [hx0] at h3 h4
    rw [abs_le]
    constructor <;> linarith
