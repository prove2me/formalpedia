-- Prove2me | solution 1 for ProbabilityTheory.map_poissonRandomMeasure_apply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:27:02.90682+00:00
-- url     : https://prove2.me/submissions/0812e59d-defb-476c-a396-9efa897844e9

import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PrMPartialCount
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
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

private lemma map_toReal_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    (μ.map fun ω => (poissonRandomMeasure K X ω A).toReal)
      = (poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ) := by
  have hN_meas : Measurable fun ω => (poissonRandomMeasure K X ω A).toReal :=
    (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA).ennreal_toReal
  haveI : IsProbabilityMeasure (μ.map fun ω => (poissonRandomMeasure K X ω A).toReal) :=
    Measure.isProbabilityMeasure_map hN_meas.aemeasurable
  haveI : IsProbabilityMeasure ((poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ)) :=
    Measure.isProbabilityMeasure_map measurable_from_top.aemeasurable
  apply Measure.ext_of_charFun
  funext ξ
  rw [charFun_natCast_poissonRandomMeasure_apply hd hA hfin, charFun_poissonMeasure_eq,
    ENNReal.coe_toNNReal_eq_toReal]

theorem solution [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) (hfin : m A < ⊤) :
    μ.map (fun ω => poissonRandomMeasure K X ω A)
      = (poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) := by
  have hN_meas : Measurable fun ω => (poissonRandomMeasure K X ω A).toReal :=
    (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA).ennreal_toReal
  have hRlaw := map_toReal_poissonRandomMeasure_apply hd hA hfin
  have hae : (fun ω => poissonRandomMeasure K X ω A)
      =ᵐ[μ] fun ω => ENNReal.ofReal ((poissonRandomMeasure K X ω A).toReal) := by
    filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hA hfin] with ω hω
    rw [ENNReal.ofReal_toReal hω.ne]
  rw [Measure.map_congr hae,
    show (fun ω => ENNReal.ofReal ((poissonRandomMeasure K X ω A).toReal))
      = ENNReal.ofReal ∘ fun ω => (poissonRandomMeasure K X ω A).toReal from rfl,
    ← Measure.map_map ENNReal.continuous_ofReal.measurable hN_meas, hRlaw,
    Measure.map_map ENNReal.continuous_ofReal.measurable measurable_from_top]
  congr 1
  funext n
  rw [Function.comp_apply, ENNReal.ofReal_natCast]
