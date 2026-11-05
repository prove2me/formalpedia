-- Prove2me | solution 1 for ProbabilityTheory.charFunDual_pi_thinnedCount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:40:55.777449+00:00
-- url     : https://prove2.me/submissions/cfeb9d70-d0e4-410a-8d41-246a37b6809c

import Theorems.Thm_ProbabilityTheory_integral_prod_pow_thinnedCount
import Definitions.Def_LeanLevy_Probability_Poisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Disjointed
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory MeasureTheory Complex
open scoped ENNReal NNReal

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω} {k : ℕ}

private lemma real_dual_apply (M : StrongDual ℝ ℝ) (r : ℝ) : M r = r * M 1 := by
  conv_rhs => rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

private lemma pi_dual_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    L x = ∑ i, x i * L (Pi.single i 1) := by
  rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => ℝ) L x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_dual_apply (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)) (x i)]
  rfl

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) => (thinnedCount K X (A i) k ω : ℝ)) L
      = ∏ i, Complex.exp ((m (prmPiece m k ∩ A i)).toReal
          * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1)) := by
  have hT : ∀ i, Measurable (thinnedCount K X (A i) k) := fun i =>
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) (hA i)
  rw [charFunDual_apply, integral_map
      (φ := fun ω (i : ι) => (thinnedCount K X (A i) k ω : ℝ))
      (measurable_pi_lambda _ fun i => (measurable_from_top.comp (hT i))).aemeasurable (by fun_prop)]
  have hpow : ∀ ω, Complex.exp (↑(L fun i => (thinnedCount K X (A i) k ω : ℝ)) * I)
      = ∏ i, (Complex.exp (↑(L (Pi.single i 1)) * I)) ^ (thinnedCount K X (A i) k ω) := by
    intro ω
    rw [pi_dual_apply L (fun i => (thinnedCount K X (A i) k ω : ℝ)),
      show (↑(∑ i, (thinnedCount K X (A i) k ω : ℝ) * L (Pi.single i 1)) : ℂ) * I
          = ∑ i, ↑(thinnedCount K X (A i) k ω) * (↑(L (Pi.single i 1)) * I) from by
        push_cast; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring,
      Complex.exp_sum]
    exact Finset.prod_congr rfl fun i _ => Complex.exp_nat_mul _ _
  simp_rw [hpow]
  exact integral_prod_pow_thinnedCount hd hA hdisj
    (fun i => Complex.exp (↑(L (Pi.single i 1)) * I))
    (fun i => le_of_eq (Complex.norm_exp_ofReal_mul_I _))
