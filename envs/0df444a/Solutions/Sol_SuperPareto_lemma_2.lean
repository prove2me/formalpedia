-- Prove2me | solution 1 for SuperPareto.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T10:46:21.985751+00:00
-- url     : https://prove2.me/submissions/df1e4cf9-649c-4e39-83cb-5c506298be06

import Mathlib
import Definitions.Def_StarShapedRisk_LawInvariant_VaR

open MeasureTheory ProbabilityTheory

theorem solution {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [Fintype ι] (Y : Ω → ℝ) (Ys : ι → Ω → ℝ) (hY : Measurable Y) (hYs : ∀ i, Measurable (Ys i))
    (θ : ι → ℝ) (hθ : θ ∈ stdSimplex ℝ ι)
    (hdom : StarShapedRisk.LawInvariant.FSD P Y (fun ω => ∑ i, θ i * Ys i ω))
    (f : ℝ → ℝ) (hfmono : Monotone f) (hfconv : ConvexOn ℝ Set.univ f) :
    StarShapedRisk.LawInvariant.FSD P (fun ω => f (Y ω))
      (fun ω => ∑ i, θ i * f (Ys i ω)) := by
  intro x
  have hcont : Continuous f :=
    continuousOn_univ.mp (hfconv.continuousOn isOpen_univ)
  have hJ : ∀ ω, f (∑ i, θ i * Ys i ω) ≤ ∑ i, θ i * f (Ys i ω) := by
    intro ω
    have := hfconv.map_sum_le (t := Finset.univ) (w := θ) (p := fun i => Ys i ω)
      (fun i _ => hθ.1 i) hθ.2 (fun i _ => Set.mem_univ _)
    simpa only [smul_eq_mul] using this
  have hsub : {ω | ∑ i, θ i * f (Ys i ω) ≤ x} ⊆ {ω | f (∑ i, θ i * Ys i ω) ≤ x} :=
    fun ω hω => (hJ ω).trans hω
  refine (measure_mono hsub).trans ?_
  have hclosed : IsClosed {t : ℝ | f t ≤ x} := isClosed_le hcont continuous_const
  by_cases hne : ∃ t, f t ≤ x
  · by_cases hbdd : BddAbove {t : ℝ | f t ≤ x}
    · have hsA : sSup {t : ℝ | f t ≤ x} ∈ {t : ℝ | f t ≤ x} :=
        hclosed.csSup_mem hne hbdd
      have hiff : ∀ t, f t ≤ x ↔ t ≤ sSup {t : ℝ | f t ≤ x} :=
        fun t => ⟨fun h => le_csSup hbdd h, fun h => (hfmono h).trans hsA⟩
      have e1 : {ω | f (∑ i, θ i * Ys i ω) ≤ x} =
          {ω | ∑ i, θ i * Ys i ω ≤ sSup {t : ℝ | f t ≤ x}} := by
        ext ω; simp only [Set.mem_setOf_eq]; exact hiff _
      have e2 : {ω | f (Y ω) ≤ x} = {ω | Y ω ≤ sSup {t : ℝ | f t ≤ x}} := by
        ext ω; simp only [Set.mem_setOf_eq]; exact hiff _
      rw [e1, e2]
      exact hdom _
    · have hall : ∀ t, f t ≤ x := by
        intro t
        rw [not_bddAbove_iff] at hbdd
        obtain ⟨a, ha, hta⟩ := hbdd t
        exact (hfmono hta.le).trans ha
      have e2 : {ω | f (Y ω) ≤ x} = Set.univ := by
        ext ω; simp [hall]
      rw [e2, measure_univ]
      exact prob_le_one
  · push_neg at hne
    have e1 : {ω | f (∑ i, θ i * Ys i ω) ≤ x} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact hne _
    rw [e1, measure_empty]
    exact zero_le
