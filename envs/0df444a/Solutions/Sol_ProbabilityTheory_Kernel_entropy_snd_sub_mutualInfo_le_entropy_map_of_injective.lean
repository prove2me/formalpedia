-- Prove2me | solution 1 for ProbabilityTheory.Kernel.entropy_snd_sub_mutualInfo_le_entropy_map_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:10:41.337366+00:00
-- url     : https://prove2.me/submissions/e622ae50-59d3-4385-b98d-f24fc8503f0d

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Theorems.Thm_ProbabilityTheory_Kernel_mutualInfo_eq_snd_sub
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_condKernel_le_entropy_snd
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_snd
public import Theorems.Thm_ProbabilityTheory_Kernel_FiniteKernelSupport_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_condKernel_map_prodMk_left
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_congr
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prod
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_snd_compProd_deterministic_of_injective
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_kernel
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
public import Theorems.Thm_ProbabilityTheory_Kernel_nonempty_of_isProbabilityMeasure_of_isMarkovKernel
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteMiddle_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteRight_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_snd_reverse
attribute [local simp] P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
attribute [local simp] ProbabilityTheory.Kernel.entropy_compProd_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_const
attribute [local simp] ProbabilityTheory.Kernel.entropy_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_prod
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkLeft
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkRight
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_kernel
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_measure
attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteMiddle_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteRight_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_snd_reverse



set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}
variable [MeasurableSingletonClass S] [MeasurableSingletonClass U]
variable [MeasurableSingletonClass T]
variable [Countable S] [Countable T]
variable [Countable U]
namespace ProbabilityTheory.Kernel
theorem _root_.solution {V : Type*} [Countable V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (κ : Kernel T (S × U)) [IsZeroOrMarkovKernel κ] (μ :
      Measure T) [IsZeroOrProbabilityMeasure μ]
    (f : S × U → V) (hfi : ∀ x, Injective (fun y ↦ f (x, y))) [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[snd κ, μ] - Ik[κ, μ] ≤ Hk[map κ f, μ] := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ'
  · simp
  have : Nonempty (S × U) := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ κ
  inhabit (S × U)
  have : Nonempty U := ⟨(default : S × U).2⟩
  have : Nonempty V := ⟨f default⟩
  rw [mutualInfo_eq_snd_sub hκ]
  have hf : Measurable f := by fun_prop
  ring_nf
  calc
    Hk[condKernel κ, μ ⊗ₘ fst κ] = Hk[snd ((condKernel κ) ⊗ₖ
        (deterministic (fun x : (T × S) × U ↦ f (x.1.2, x.2))
        .of_discrete)), μ ⊗ₘ fst κ] := by
      symm
      apply entropy_snd_compProd_deterministic_of_injective _ _ (fun t ↦ hfi t.2)
    _ = Hk[condKernel (map κ (fun p ↦ (p.1, f p))),
      μ ⊗ₘ fst κ] := entropy_congr (condKernel_map_prodMk_left κ μ f).symm
    _ = Hk[condKernel (map κ (fun p ↦ (p.1, f p))),
      μ ⊗ₘ fst (map κ (fun p ↦ (p.1, f p)))] := by
        congr 2 with x
        rw [fst_map_prod _ hf, fst_apply, map_apply _ measurable_fst]
    _ ≤ Hk[snd (map κ (fun p ↦ (p.1, f p))), μ] :=
      entropy_condKernel_le_entropy_snd hκ.map
    _ = Hk[map κ f, μ] := by rw [snd_map_prod _ measurable_fst]
end ProbabilityTheory.Kernel
