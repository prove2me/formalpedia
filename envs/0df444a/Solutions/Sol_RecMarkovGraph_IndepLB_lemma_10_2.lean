-- Prove2me | solution 1 for RecMarkovGraph.IndepLB.lemma_10_2
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T15:00:22.073171+00:00
-- url     : https://prove2.me/submissions/152d0f9f-0386-474d-9dc6-daa72899d172

import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_10_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hX0 : ∀ n, 0 ≤ᵐ[P] X n)
    (hX2 : ∀ᶠ n in atTop, MemLp (X n) 2 P) (hμ : ∀ n, 0 < ∫ ω, X n ω ∂P)
    (hσ : (fun n => variance (X n) P) =o[atTop] (fun n => (∫ ω, X n ω ∂P) ^ 2)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P.real {ω | |X n ω / ∫ ω', X n ω' ∂P - 1| ≤ ε}) atTop (𝓝 1) := by
  intro ε hε
  have hratio : Tendsto (fun n => variance (X n) P / (∫ ω, X n ω ∂P) ^ 2) atTop (𝓝 0) :=
    hσ.tendsto_div_nhds_zero
  have hlow : Tendsto (fun n => 1 - (variance (X n) P / (∫ ω, X n ω ∂P) ^ 2) / ε ^ 2)
      atTop (𝓝 1) := by
    have := (hratio.div_const (ε ^ 2)).const_sub 1
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun n => measureReal_le_one)
  filter_upwards [hX2] with n hn
  set m := ∫ ω, X n ω ∂P with hm
  have hmpos : 0 < m := hμ n
  have hc : 0 < ε * m := mul_pos hε hmpos
  set s := {ω | |X n ω / m - 1| ≤ ε} with hs
  have hsm : MeasurableSet s :=
    measurableSet_le (((hXm n).div_const m).sub_const 1).abs measurable_const
  have hsub : sᶜ ⊆ {ω | ε * m ≤ |X n ω - ∫ ω', X n ω' ∂P|} := by
    intro ω hω
    simp only [hs, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
    rw [← hm]
    have : X n ω / m - 1 = (X n ω - m) / m := by field_simp
    rw [this, abs_div, abs_of_pos hmpos, lt_div_iff₀ hmpos] at hω
    linarith
  have hcheb := meas_ge_le_variance_div_sq hn hc
  have hvar : 0 ≤ variance (X n) P := variance_nonneg _ _
  have h1 : P.real sᶜ ≤ variance (X n) P / (ε * m) ^ 2 := by
    calc P.real sᶜ ≤ P.real {ω | ε * m ≤ |X n ω - ∫ ω', X n ω' ∂P|} :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ variance (X n) P / (ε * m) ^ 2 := by
          rw [measureReal_def]
          have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
          rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have h2 : P.real sᶜ = 1 - P.real s := by
    rw [measureReal_compl hsm, probReal_univ]
  have h3 : variance (X n) P / (ε * m) ^ 2 = variance (X n) P / m ^ 2 / ε ^ 2 := by
    rw [mul_pow, div_div, mul_comm]
  linarith

end RecMarkovGraph.IndepLB


-- Platform entry point: restates the target verbatim.
namespace RecMarkovGraph.IndepLB

open MeasureTheory ProbabilityTheory Filter Topology

theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hX0 : ∀ n, 0 ≤ᵐ[P] X n)
    (hX2 : ∀ᶠ n in atTop, MemLp (X n) 2 P) (hμ : ∀ n, 0 < ∫ ω, X n ω ∂P)
    (hσ : (fun n => variance (X n) P) =o[atTop] (fun n => (∫ ω, X n ω ∂P) ^ 2)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P.real {ω | |X n ω / ∫ ω', X n ω' ∂P - 1| ≤ ε}) atTop (𝓝 1) := by
  apply @RecMarkovGraph.IndepLB.lemma_10_2 <;> assumption

end RecMarkovGraph.IndepLB
