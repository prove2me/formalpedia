-- Prove2me | solution 1 for StochKolmogorov.Classify.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T22:24:03.29808+00:00
-- url     : https://prove2.me/submissions/5661647c-0d33-41f8-88bc-62a5dab08e4d

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification
import Definitions.Def_StochKolmogorov_Persist_Model
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_3

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

set_option autoImplicit false

namespace ClassifyL33

/-- The same coefficients, read in the `Persist` copy of the model. -/
def toP {n : ℕ} (C : StochKolmogorov.Classify.Coeffs n) : StochKolmogorov.Persist.Coeffs n :=
  ⟨C.f, C.g, C.Γ⟩

open EthierKurtz StochKolmogorov.Classify in
/-- `growthWeight` with `gᵢ²` written as `|gᵢ|²`, as in the Persist statement. -/
theorem growthWeight_eq {n : ℕ} (C : Coeffs n) (c : SDEState n) (δ₀ : ℝ) (y : SDEState n) :
    growthWeight C c δ₀ y =
      (1 + ∑ i, c i * y i) ^ δ₀ * (1 + ∑ i, (|(toP C).f i y| + |(toP C).g i y| ^ 2)) := by
  simp only [growthWeight, sq_abs, toP]

open EthierKurtz StochKolmogorov.Classify in
theorem l33 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (H₂ : ℝ) (hH₂ : 0 < H₂)
    (h38 : ∀ x ∈ orthant n, ∀ t : ℝ, 0 < t →
      ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
          ENNReal.ofReal (growthWeight C c δ₀ (X x s.toNNReal ω))) ∂P
        ≤ ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + t)))
    (μ : Measure (SDEState n)) (hμ : IsInvariant P X μ) :
    ∫⁻ y, ENNReal.ofReal (growthWeight C c δ₀ y) ∂μ ≤ ENNReal.ofReal H₂ ∧
      Integrable (cBracket C c) μ ∧ ∫ y, cBracket C c y ∂μ = 0 := by
  have h38' : ∀ x ∈ StochKolmogorov.Persist.orthant n, ∀ t : ℝ≥0, 0 < t →
      ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
          ENNReal.ofReal ((1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
            (1 + ∑ i, (|(toP C).f i (X x s.toNNReal ω)| + |(toP C).g i (X x s.toNNReal ω)| ^ 2))))
          ∂P ≤
        ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + t)) := by
    intro x hx t ht
    have h := h38 x hx (t : ℝ) (by exact_mod_cast ht)
    simp only [growthWeight_eq] at h
    exact h
  have key := StochKolmogorov.Persist.lemma_3_3 hn P (toP C) B X hX c γb hA δ₀ hδ₀ H₂ hH₂ h38' μ hμ
  refine ⟨?_, key.2.1, key.2.2⟩
  simp only [growthWeight_eq]
  exact key.1

end ClassifyL33

open StochKolmogorov.Classify EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (H₂ : ℝ) (hH₂ : 0 < H₂)
    (h38 : ∀ x ∈ orthant n, ∀ t : ℝ, 0 < t →
      ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
          ENNReal.ofReal (growthWeight C c δ₀ (X x s.toNNReal ω))) ∂P
        ≤ ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + t)))
    (μ : Measure (SDEState n)) (hμ : IsInvariant P X μ) :
    ∫⁻ y, ENNReal.ofReal (growthWeight C c δ₀ y) ∂μ ≤ ENNReal.ofReal H₂ ∧
      Integrable (cBracket C c) μ ∧ ∫ y, cBracket C c y ∂μ = 0 := by
  exact ClassifyL33.l33 hn P C B X hX c γb hA δ₀ hδ₀ H₂ hH₂ h38 μ hμ
