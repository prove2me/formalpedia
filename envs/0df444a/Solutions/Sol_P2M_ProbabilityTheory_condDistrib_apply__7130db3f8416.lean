-- Prove2me | solution 1 for P2M_ProbabilityTheory_condDistrib_apply__7130db3f8416
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:31:30.091886+00:00
-- url     : https://prove2.me/submissions/2df94a4b-d9e8-4a17-b1e4-0166c6947fce

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace T] [MeasurableSpace U]
variable [MeasurableSingletonClass T]
variable [Countable U] [DiscreteMeasurableSpace U]
variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution
    [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ] (x : T) (hYx : μ (Y ⁻¹' {x}) ≠ 0) {s : Set S} (hs :
      MeasurableSet s) :
    condDistrib X Y μ x s = (μ (Y ⁻¹' {x}))⁻¹ * μ (Y ⁻¹' {x} ∩ X ⁻¹' s) := by
  have hx : μ.map Y {x} ≠ 0 := by
    rwa [Measure.map_apply hY (.singleton _)]
  rw [condDistrib_apply_of_ne_zero hX x hx s,
    Measure.map_apply hY (.singleton _),
    Measure.map_apply (hY.prodMk hX) ((measurableSet_singleton _).prod hs)]
  rfl
end _root_.ProbabilityTheory
end ProbabilityTheory
