-- Prove2me | solution 1 for ProbabilityTheory.iIndepFun_natCast_poissonRandomMeasure_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:26:53.195344+00:00
-- url     : https://prove2.me/submissions/a95218fb-ae75-44d3-88d8-458368dbd117

import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PrMPartialCount
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Theorems.Thm_ProbabilityTheory_charFunDual_poissonRandomMeasureVec
import Theorems.Thm_ProbabilityTheory_charFun_natCast_poissonRandomMeasure_apply
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Complex ProbabilityTheory
open scoped ENNReal NNReal Topology
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E]
  {μ : Measure Ω} {A B : Set E} {ω : Ω}
private lemma real_dual_apply (M : StrongDual ℝ ℝ) (r : ℝ) : M r = r * M 1 := by
  conv_rhs => rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

private lemma charFunDual_real_eq_charFun (ν : Measure ℝ) (M : StrongDual ℝ ℝ) :
    charFunDual ν M = charFun ν (M 1) := by
  rw [charFunDual_apply, charFun_apply_real]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Complex.exp (↑(M x) * I) = Complex.exp (↑(M 1) * ↑x * I)
  rw [real_dual_apply M x]
  congr 1
  push_cast
  ring

theorem solution {ι : Type} [Fintype ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, m (A i) < ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    iIndepFun (fun i ω => (poissonRandomMeasure K X ω (A i)).toReal) μ := by
  classical
  rw [iIndepFun_iff_charFunDual_pi
    (X := fun i ω => (poissonRandomMeasure K X ω (A i)).toReal)
    fun i => (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point
      (hA i)).ennreal_toReal.aemeasurable]
  intro L
  rw [charFunDual_poissonRandomMeasureVec hd hA hfin hdisj L]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [charFunDual_real_eq_charFun, charFun_natCast_poissonRandomMeasure_apply hd (hA i) (hfin i)]
  rfl
