-- Prove2me | solution 1 for ProbabilityTheory.condDistrib_const_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:39:15.680509+00:00
-- url     : https://prove2.me/submissions/85ed134b-6570-4769-a02c-1f714864388b

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Theorems.Thm_P2M_ProbabilityTheory_Kernel_condKernel_apply__e1c6db4f1898
public import Theorems.Thm_P2M_ProbabilityTheory_condDistrib_apply__7130db3f8416

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
variable [Countable T]
variable [Nonempty T]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Kernel.condKernel (Kernel.const Unit (μ.map (fun ω ↦ (X ω, Y ω))))
      =ᵐ[μ.map (fun ω ↦ ((), X ω))] Kernel.prodMkLeft Unit (condDistrib Y X μ) := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  have : (fun a ↦ ((), X a)) ⁻¹' {x} = X ⁻¹' {x.2} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Prod.eta x, Prod.mk_inj]
    simp
  rw [Measure.map_apply (measurable_const.prodMk hX) (.singleton _), this] at hx
  ext s hs
  rw [Kernel.condKernel_apply']
  swap
  · rw [Kernel.const_apply,
      Measure.map_apply (hX.prodMk hY) (measurable_fst (.singleton _))]
    exact hx
  simp_rw [Kernel.const_apply,
    Measure.map_apply (hX.prodMk hY) (measurable_fst (.singleton _)),
    Measure.map_apply (hX.prodMk hY) ((measurableSet_singleton _).prod hs)]
  rw [Kernel.prodMkLeft_apply', condDistrib_apply' hY hX _ _ hx hs]
  rfl
end _root_.ProbabilityTheory
end ProbabilityTheory
