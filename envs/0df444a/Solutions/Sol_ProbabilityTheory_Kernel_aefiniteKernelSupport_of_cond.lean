-- Prove2me | solution 1 for ProbabilityTheory.Kernel.aefiniteKernelSupport_of_cond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:38:57.683326+00:00
-- url     : https://prove2.me/submissions/ed75f119-d81b-47cb-86fd-388524692efd

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Theorems.Thm_P2M_ProbabilityTheory_Kernel_condKernel_apply__e1c6db4f1898
public import Theorems.Thm_MeasureTheory_Measure_compProd_apply_singleton
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_snd

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
namespace ProbabilityTheory.Kernel
namespace _root_.ProbabilityTheory.Kernel
theorem _root_.solution
    {κ : Kernel T (S × U)} [hU : Nonempty U]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U] [Countable U] [Countable S] [Countable T]
    (μ : Measure T) (hκ : AEFiniteKernelSupport κ μ) [IsFiniteKernel κ] :
    AEFiniteKernelSupport (condKernel κ) (μ ⊗ₘ (Kernel.fst κ)) := by
  rw [AEFiniteKernelSupport, ae_iff_of_countable] at hκ ⊢
  intro (t, s) hts
  simp only [compProd_apply_singleton, ne_eq, mul_eq_zero, not_or] at hts
  push Not at hts
  rcases hκ t hts.2 with ⟨A, hA⟩
  classical
  use Finset.image Prod.snd A
  rw [condKernel_apply']; swap
  · rw [Kernel.fst_apply' _ _ (.singleton _)] at hts
    exact hts.1
  simp only [Finset.coe_image, Set.singleton_prod, mul_eq_zero, ENNReal.inv_eq_zero]
  right
  refine measure_mono_null ?_ hA
  intro x
  simp only [Set.mem_image, Set.mem_compl_iff, Finset.mem_coe, Prod.exists, exists_eq_right,
    not_exists, forall_exists_index, and_imp]
  intro y h hsyx
  rw [← hsyx]
  exact h s
end _root_.ProbabilityTheory.Kernel
end ProbabilityTheory.Kernel
