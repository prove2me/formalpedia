-- Prove2me | solution 1 for TierneyMH.Peskun.lemma3_positive_operator
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:31:30.508129+00:00
-- url     : https://prove2.me/submissions/0b87c09b-9473-44ef-9eb8-091f96483426

import Definitions.Def_TierneyMH_Shared_OffDiagDominates
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open TierneyMH.Shared

namespace PeskunProof
variable {E : Type*} [MeasurableSpace E]

theorem fst_preserving (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] : MeasurePreserving Prod.fst (π ⊗ₘ P) π :=
  ⟨measurable_fst, Measure.fst_compProd π P⟩

theorem snd_preserving (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] (hi : Kernel.Invariant P π) :
    MeasurePreserving Prod.snd (π ⊗ₘ P) π :=
  ⟨measurable_snd, (Measure.snd_compProd π P).trans hi⟩

theorem integral_preserving {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (T : A → B) (hT : MeasurePreserving T μ ν)
    (g : B → ℝ) (hg : Measurable g) : ∫ x, g (T x) ∂μ = ∫ y, g y ∂ν := by
  calc
    ∫ x, g (T x) ∂μ = ∫ y, g y ∂μ.map T :=
      (integral_map hT.measurable.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂ν := by rw [hT.map_eq]

theorem joint_memLp (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] (hi : Kernel.Invariant P π)
    (f : E → ℝ) (hf : MemLp f 2 π) :
    MemLp (fun p : E × E => f p.1) 2 (π ⊗ₘ P) ∧
      MemLp (fun p : E × E => f p.2) 2 (π ⊗ₘ P) :=
  ⟨hf.comp_measurePreserving (fst_preserving π P),hf.comp_measurePreserving (snd_preserving π P hi)⟩

theorem energy_integrable (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] (hi : Kernel.Invariant P π)
    (f : E → ℝ) (hf : MemLp f 2 π) :
    Integrable (fun p : E × E => (f p.1-f p.2)^2) (π ⊗ₘ P) := by
  obtain ⟨h1,h2⟩ := joint_memLp π P hi f hf
  exact (h1.sub h2).integrable_sq

theorem energy_identity (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] (hi : Kernel.Invariant P π)
    (f : E → ℝ) (hm : Measurable f) (hf : MemLp f 2 π) :
    (∫ p, (f p.1-f p.2)^2 ∂π ⊗ₘ P) =
      2*(∫ x, f x^2 ∂π)-2*(∫ p, f p.1*f p.2 ∂π ⊗ₘ P) := by
  obtain ⟨h1,h2⟩ := joint_memLp π P hi f hf
  have hp : (fun p : E × E => (f p.1-f p.2)^2) =
      (fun p => f p.1^2+f p.2^2-2*(f p.1*f p.2)) := by funext p; ring
  have hs := integral_sub (h1.integrable_sq.add h2.integrable_sq) ((h1.integrable_mul h2).const_mul 2)
  have ha := integral_add h1.integrable_sq h2.integrable_sq
  simp only [Pi.add_apply,Pi.mul_apply] at hs ha
  rw [hp, hs, ha, integral_const_mul]
  rw [integral_preserving _ _ _ (fst_preserving π P) (fun x => f x^2) (hm.pow_const 2),
    integral_preserving _ _ _ (snd_preserving π P hi) (fun x => f x^2) (hm.pow_const 2)]
  ring

theorem remove_diagonal [MeasurableSingletonClass E] (μ : Measure E) (f : E → ℝ) (x : E) :
    (∫ y in ({x} : Set E)ᶜ, (f x-f y)^2 ∂μ) = ∫ y, (f x-f y)^2 ∂μ := by
  rw [← integral_indicator (measurableSet_singleton x).compl]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    by_cases h : y=x
    · subst y; simp
    · simp [h]

theorem offdiag_restrict [MeasurableSingletonClass E] (μ ν : Measure E) (x : E)
    (h : ∀ A : Set E, MeasurableSet A → μ (A \ {x}) ≤ ν (A \ {x})) :
    μ.restrict ({x} : Set E)ᶜ ≤ ν.restrict ({x} : Set E)ᶜ := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA,Measure.restrict_apply hA]
  simpa only [Set.diff_eq] using h A hA

theorem positive_operator [MeasurableSingletonClass E]
    (π : Measure E) [IsProbabilityMeasure π]
    (P₁ P₂ : Kernel E E) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (hi1 : Kernel.Invariant P₁ π) (hi2 : Kernel.Invariant P₂ π)
    (hd : OffDiagDominates π P₁ P₂)
    (f : E → ℝ) (hm : Measurable f) (hf : MemLp f 2 π) :
    0 ≤ (∫ p, f p.1*f p.2 ∂π ⊗ₘ P₂) - ∫ p, f p.1*f p.2 ∂π ⊗ₘ P₁ := by
  have h1 := energy_integrable π P₁ hi1 f hf
  have h2 := energy_integrable π P₂ hi2 f hf
  have he1 := (Measure.integrable_compProd_iff h1.aestronglyMeasurable).mp h1
  have he2 := (Measure.integrable_compProd_iff h2.aestronglyMeasurable).mp h2
  have hout1 : Integrable (fun x => ∫ y, (f x-f y)^2 ∂P₁ x) π := by
    simpa only [Real.norm_eq_abs,abs_sq] using he1.2
  have hout2 : Integrable (fun x => ∫ y, (f x-f y)^2 ∂P₂ x) π := by
    simpa only [Real.norm_eq_abs,abs_sq] using he2.2
  have hle : (∫ p, (f p.1-f p.2)^2 ∂π ⊗ₘ P₂) ≤ ∫ p, (f p.1-f p.2)^2 ∂π ⊗ₘ P₁ := by
    rw [Measure.integral_compProd h1,Measure.integral_compProd h2]
    apply integral_mono_ae hout2 hout1
    filter_upwards [hd,he1.1] with x hx hxi
    rw [← remove_diagonal (P₁ x) f x,← remove_diagonal (P₂ x) f x]
    exact integral_mono_measure (offdiag_restrict _ _ x hx)
      (Eventually.of_forall fun y => sq_nonneg _) hxi.restrict
  rw [energy_identity π P₁ hi1 f hm hf,energy_identity π P₂ hi2 f hm hf] at hle
  linarith
end PeskunProof



/-- **Lemma 3** (Tierney 1998, p. 5). Let `P₁ P₂` be Markov kernels on `E` with invariant
distribution `π` (invariance only, not reversibility, as printed), and suppose `P₁ ⪰ P₂`
(`OffDiagDominates π P₁ P₂`). Then `P₂ − P₁` is a positive operator on `L²(π)`: for every
`f ∈ L²(π)`,
`⟨(P₂ − P₁) f, f⟩ = ∬ f(x) f(y) (P₂(x, dy) − P₁(x, dy)) π(dx) ≥ 0`.
The double integral against `P₂(x, dy) − P₁(x, dy)` is written as the difference of the
integrals of `f(x) f(y)` against the joint laws `π ⊗ₘ P₂` and `π ⊗ₘ P₁`; both have marginals
`π` by invariance, so `f(x) f(y)` is integrable against each and neither integral is Lean's
junk value `0`. `MeasurableSingletonClass E` is the paper's implicit assumption that
`A \ {x}` is an event; `Measurable f` picks a measurable version of the `L²` class. -/
theorem solution {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    (π : Measure E) [IsProbabilityMeasure π]
    (P₁ P₂ : Kernel E E) [IsMarkovKernel P₁] [IsMarkovKernel P₂]
    (hinv₁ : Kernel.Invariant P₁ π) (hinv₂ : Kernel.Invariant P₂ π)
    (hdom : OffDiagDominates π P₁ P₂)
    (f : E → ℝ) (hf_meas : Measurable f) (hf : MemLp f 2 π) :
    0 ≤ (∫ p, f p.1 * f p.2 ∂(π ⊗ₘ P₂)) - ∫ p, f p.1 * f p.2 ∂(π ⊗ₘ P₁) := by
  exact PeskunProof.positive_operator π P₁ P₂ hinv₁ hinv₂ hdom f hf_meas hf


