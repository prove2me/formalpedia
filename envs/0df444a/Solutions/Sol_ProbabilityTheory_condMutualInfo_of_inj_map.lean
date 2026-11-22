-- Prove2me | solution 1 for ProbabilityTheory.condMutualInfo_of_inj_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:09:48.791804+00:00
-- url     : https://prove2.me/submissions/73ab3636-f4d4-4785-94bb-c180fb15f16c

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_condEntropy_of_injective
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_eq
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk


set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
variable [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]
variable [Countable S] [Countable T]
variable [MeasurableSingletonClass U]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution
    [Countable U] [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (f : U → S → V) (hf : ∀ t, Function.Injective (f t)) [FiniteRange Z] :
    I[fun ω ↦ f (Z ω) (X ω) : Y | Z; μ] =
    I[X : Y | Z; μ] := by
  have hM : Measurable (Function.uncurry f ∘ ⟨Z, X⟩) := by fun_prop
  have hM : Measurable fun ω ↦ f (Z ω) (X ω) := hM
  rw [condMutualInfo_eq hM hY hZ, condMutualInfo_eq hX hY hZ]
  let g : U → (S × T) → (V × T) := fun z (x, y) ↦ (f z x, y)
  have hg : ∀ t, Function.Injective (g t) :=
    fun _ _ _ h ↦ Prod.ext_iff.2 ⟨hf _ (Prod.ext_iff.1 h).1, (Prod.ext_iff.1 h).2⟩
  rw [← condEntropy_of_injective μ (hX.prodMk hY) hZ g hg,
    ← condEntropy_of_injective μ hX hZ _ hf]
end _root_.ProbabilityTheory
end ProbabilityTheory
