-- Prove2me | solution 1 for RecMarkovGraph.IndepLB.lemma_10_3
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T14:58:30.971735+00:00
-- url     : https://prove2.me/submissions/0a724234-02c7-47c7-b14c-6806afee9788

import Definitions.Def_RecMarkovGraph_IndepLB_Model

namespace RecMarkovGraph.IndepLB

open MeasureTheory Filter Topology

theorem lemma_10_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (Z : ℕ → ℝ) (hZ : ∀ n, 0 < Z n)
    (τ : ℝ) (hZτ : Tendsto Z atTop (𝓝 τ)) (lam : ℝ) (hlam : 0 < lam)
    (hconv : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P.real {ω | |X n ω / Z n - lam| ≤ ε}) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P.real {ω | |X n ω - lam * τ| ≤ ε}) atTop (𝓝 1) := by
  intro ε hε
  have hτ : 0 ≤ τ := ge_of_tendsto hZτ (Eventually.of_forall fun n => (hZ n).le)
  set δ := ε / (2 * (τ + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδτ : (τ + 1) * δ = ε / 2 := by rw [hδ]; field_simp
  have hev : ∀ᶠ n in atTop, |Z n - τ| < min 1 (ε / (2 * lam)) := by
    have := (Metric.tendsto_nhds.mp hZτ) (min 1 (ε / (2 * lam))) (by positivity)
    simpa [Real.dist_eq] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hconv δ hδpos) tendsto_const_nhds ?_
    (Eventually.of_forall fun n => measureReal_le_one)
  filter_upwards [hev] with n hn
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hZn := hZ n
  have h1 : |Z n - τ| < 1 := lt_of_lt_of_le hn (min_le_left _ _)
  have h2 : |Z n - τ| < ε / (2 * lam) := lt_of_lt_of_le hn (min_le_right _ _)
  have hZle : Z n ≤ τ + 1 := by linarith [le_abs_self (Z n - τ)]
  have hid : X n ω - lam * τ = Z n * (X n ω / Z n - lam) + lam * (Z n - τ) := by
    field_simp; ring
  rw [hid]
  calc |Z n * (X n ω / Z n - lam) + lam * (Z n - τ)|
      ≤ |Z n * (X n ω / Z n - lam)| + |lam * (Z n - τ)| := abs_add_le _ _
    _ = Z n * |X n ω / Z n - lam| + lam * |Z n - τ| := by
        rw [abs_mul, abs_mul, abs_of_pos hZn, abs_of_pos hlam]
    _ ≤ (τ + 1) * δ + lam * (ε / (2 * lam)) := by
        gcongr
    _ = ε := by rw [hδτ]; field_simp; ring

end RecMarkovGraph.IndepLB


-- Platform entry point: restates the target verbatim.
namespace RecMarkovGraph.IndepLB

open MeasureTheory Filter Topology

theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (Z : ℕ → ℝ) (hZ : ∀ n, 0 < Z n)
    (τ : ℝ) (hZτ : Tendsto Z atTop (𝓝 τ)) (lam : ℝ) (hlam : 0 < lam)
    (hconv : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P.real {ω | |X n ω / Z n - lam| ≤ ε}) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P.real {ω | |X n ω - lam * τ| ≤ ε}) atTop (𝓝 1) := by
  apply @RecMarkovGraph.IndepLB.lemma_10_3 <;> assumption

end RecMarkovGraph.IndepLB
