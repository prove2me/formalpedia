-- Prove2me | solution 1 for StochIneqPO.Comparison.corollary1_iii
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T17:37:15.63312+00:00
-- url     : https://prove2.me/submissions/5f0f60f9-7fe7-4809-91bc-8e119ce4d6a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Theorems.Thm_StochIneqPO_Comparison_comparison_theorem

open MeasureTheory ProbabilityTheory Finset StochIneqPO.Comparison

theorem solution {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] [PartialOrder E] [OrderClosedTopology E]
    (P₁ Q₁ : Measure E) [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    (p q : (n : ℕ) → Kernel (Π _ : Iic n, E) E)
    [∀ n, IsMarkovKernel (p n)] [∀ n, IsMarkovKernel (q n)]
    (hPQ : StochLE P₁ Q₁)
    (hpq : ∀ n, ∀ x y : Π _ : Iic n, E, x ≤ y → StochLE (p n x) (q n y))
    (f : E → ℝ) (hf : Measurable f) (hmono : Monotone f) (n : ℕ)
    (hexP : ∫⁻ x, ENNReal.ofReal (f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) P₁ p) ≠ ⊤ ∨
      ∫⁻ x, ENNReal.ofReal (-f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) P₁ p) ≠ ⊤)
    (hexQ : ∫⁻ x, ENNReal.ofReal (f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) Q₁ q) ≠ ⊤ ∨
      ∫⁻ x, ENNReal.ofReal (-f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) Q₁ q) ≠ ⊤) :
    ((∫⁻ x, ENNReal.ofReal (f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) P₁ p) : EReal) -
        (∫⁻ x, ENNReal.ofReal (-f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) P₁ p) : EReal)) ≤
      ((∫⁻ x, ENNReal.ofReal (f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) Q₁ q) : EReal) -
        (∫⁻ x, ENNReal.ofReal (-f (x n)) ∂(Kernel.trajMeasure (X := fun _ => E) Q₁ q) : EReal)) := by
  obtain ⟨Ω, mΩ, μ, hμ, X, Y, hX, hY, hlX, hlY, hle⟩ :=
    comparison_theorem (E := fun _ => E) P₁ Q₁ p q hPQ hpq
  have hXm : Measurable (fun ω n => X n ω) := measurable_pi_lambda _ hX
  have hYm : Measurable (fun ω n => Y n ω) := measurable_pi_lambda _ hY
  have h1 : Measurable (fun x : ℕ → E => ENNReal.ofReal (f (x n))) :=
    ENNReal.measurable_ofReal.comp (hf.comp (measurable_pi_apply n))
  have h2 : Measurable (fun x : ℕ → E => ENNReal.ofReal (-f (x n))) :=
    ENNReal.measurable_ofReal.comp ((hf.comp (measurable_pi_apply n)).neg)
  rw [← hlX, ← hlY, lintegral_map h1 hXm, lintegral_map h1 hYm, lintegral_map h2 hXm,
    lintegral_map h2 hYm]
  apply EReal.sub_le_sub
  · apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    apply lintegral_mono_ae
    filter_upwards [hle] with ω h
    exact ENNReal.ofReal_le_ofReal (hmono (h n))
  · apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    apply lintegral_mono_ae
    filter_upwards [hle] with ω h
    exact ENNReal.ofReal_le_ofReal (neg_le_neg (hmono (h n)))
