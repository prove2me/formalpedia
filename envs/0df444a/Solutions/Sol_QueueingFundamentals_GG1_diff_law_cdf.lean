-- Prove2me | solution 1 for QueueingFundamentals.GG1.diff_law_cdf
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:21:57.718616+00:00
-- url     : https://prove2.me/submissions/0a524a7e-4c24-47fe-b585-047d1745e109

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_Lindley

open MeasureTheory QueueingFundamentals.GG1 in
lemma dl5b_cdf_mono (B : Measure ℝ) [IsFiniteMeasure B] : Monotone (cdfOf B) := by
  intro a b hab
  unfold cdfOf
  exact measureReal_mono (Set.Iic_subset_Iic.mpr hab)

open MeasureTheory QueueingFundamentals.GG1 in
lemma dl5b_lhs (A B : Measure ℝ) [IsProbabilityMeasure A] [IsProbabilityMeasure B] (x : ℝ) :
    cdfOf (diffLaw A B) x = ∫ a, cdfOf B (a + x) ∂A := by
  have hmeas : Measurable (fun p : ℝ × ℝ => p.1 - p.2) := measurable_fst.sub measurable_snd
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 - p.2 ≤ x} :=
    measurableSet_le hmeas measurable_const
  unfold cdfOf diffLaw
  rw [measureReal_def, Measure.map_apply hmeas measurableSet_Iic,
    Measure.prod_apply_symm (by simpa [Set.preimage, Set.mem_Iic] using hS)]
  have hmono : Monotone (fun a : ℝ => B (Set.Iic (a + x))) := by
    intro a b hab
    exact measure_mono (Set.Iic_subset_Iic.mpr (by linarith))
  have hset : ∀ a : ℝ, (fun s : ℝ => (s, a)) ⁻¹' ((fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' Set.Iic x)
      = Set.Iic (a + x) := by
    intro a; ext s; simp [Set.mem_Iic]; constructor <;> intro h <;> linarith
  simp_rw [hset]
  rw [← integral_toReal hmono.measurable.aemeasurable
    (Filter.Eventually.of_forall (fun a => measure_lt_top _ _))]
  rfl

open MeasureTheory QueueingFundamentals.GG1 in
theorem solution (A B : Measure ℝ) (hA : IsLifetimeLaw A) (hB : IsLifetimeLaw B) (x : ℝ) :
    cdfOf (diffLaw A B) x =
      ∫ y in Set.Ici (max 0 x), cdfOf B y ∂(A.map (fun a => a + x)) := by
  obtain ⟨hAp, hA0⟩ := hA
  obtain ⟨hBp, hB0⟩ := hB
  have hg : Measurable (fun a : ℝ => a + x) := measurable_id.add_const x
  have hfm : Measurable (cdfOf B) := (dl5b_cdf_mono B).measurable
  rw [dl5b_lhs A B x]
  rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
  · rw [integral_map hg.aemeasurable hfm.aestronglyMeasurable]
  · have h0 : ∀ᵐ a ∂A, 0 ≤ a := by
      rw [ae_iff]
      have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext a; simp
      rw [this]; exact hA0
    have h1 : ∀ᵐ y ∂(A.map (fun a => a + x)), x ≤ y :=
      (ae_map_iff hg.aemeasurable (measurableSet_le measurable_const measurable_id)).mpr
        (h0.mono (fun a ha => by simp only [id]; linarith))
    filter_upwards [h1] with y hy hny
    have hy0 : y < 0 := by
      simp only [Set.mem_Ici, not_le, lt_max_iff] at hny
      rcases hny with h | h
      · exact h
      · linarith
    have hle : cdfOf B y ≤ B.real (Set.Iio 0) := by
      unfold cdfOf
      exact measureReal_mono (Set.Iic_subset_Iio.mpr hy0)
    have hz : B.real (Set.Iio 0) = 0 := by rw [measureReal_def, hB0]; rfl
    have hnn : 0 ≤ cdfOf B y := measureReal_nonneg
    linarith
