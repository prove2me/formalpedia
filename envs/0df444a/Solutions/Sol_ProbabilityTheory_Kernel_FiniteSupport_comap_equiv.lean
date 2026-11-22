-- Prove2me | solution 1 for ProbabilityTheory.Kernel.FiniteSupport.comap_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:35:34.980424+00:00
-- url     : https://prove2.me/submissions/2b810032-f5a1-46ac-8cf7-2e96b744af44

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
namespace ProbabilityTheory.Kernel
namespace _root_.ProbabilityTheory.Kernel.FiniteSupport
theorem _root_.solution [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T']
    {μ : Measure T} (f : T' ≃ᵐ T) [FiniteSupport μ] :
    FiniteSupport (μ.comap f) := by
  classical
  let A := μ.finiteSupport
  have hA := measure_compl_support μ
  refine ⟨Finset.image f.symm A, ?_⟩
  change (Measure.comap (⇑f) μ) (A.image f.symm)ᶜ = 0
  rwa [Finset.coe_image, ← Set.image_compl_eq (MeasurableEquiv.bijective f.symm),
    Measure.comap_apply f (MeasurableEquiv.injective f),MeasurableEquiv.image_symm,
    MeasurableEquiv.image_preimage]
  · exact fun _ ↦ (MeasurableEquiv.measurableSet_image f).mpr
  · exact f.symm.measurableSet_image.mpr A.measurableSet.compl
end _root_.ProbabilityTheory.Kernel.FiniteSupport
end ProbabilityTheory.Kernel
