-- Prove2me | solution 1 for P2M_ProbabilityTheory_prob_ge_exp_neg_entropy__d0720956467a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:05:20.68488+00:00
-- url     : https://prove2.me/submissions/a5531a52-b634-4f9a-b148-519468fee767

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_prob_ge_exp_neg_entropy

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
open Set
open Function
namespace ProbabilityTheory
theorem _root_.solution [MeasurableSingletonClass S]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → S) (hX : Measurable X) [FiniteRange X] :
    ∃ s : S, rexp (- H[X; μ]) ≤ μ.real (X ⁻¹' {s}) := by
  obtain ⟨s, hs⟩ := prob_ge_exp_neg_entropy X μ hX
  use s
  rwa [IsProbabilityMeasure.measure_univ, one_mul,
    (show ENNReal.ofNNReal _ = ENNReal.ofReal _ from rfl),
    ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _), ← Measure.real,
    map_measureReal_apply hX (MeasurableSet.singleton s)] at hs
end ProbabilityTheory
