-- Prove2me | solution 1 for ProbabilityTheory.Kernel.entropy_submodular_compProd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:02:24.551782+00:00
-- url     : https://prove2.me/submissions/a9d92fac-532e-44da-b272-e4ec04c2eeca

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Theorems.Thm_P2M_ProbabilityTheory_Kernel_Measure_compProd_compProd___39a21c44794a
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_condKernel_le_entropy_snd
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_comap_equiv
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_compProd
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_snd
public import Theorems.Thm_ProbabilityTheory_Kernel_FiniteKernelSupport_compProd
public import Theorems.Thm_ProbabilityTheory_Kernel_FiniteSupport_comap_equiv
public import Theorems.Thm_ProbabilityTheory_Kernel_condKernel_compProd_ae_eq
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_comap_equiv
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_congr
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prod
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_kernel
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
public import Theorems.Thm_ProbabilityTheory_Kernel_finiteSupport_of_compProd
public import Theorems.Thm_ProbabilityTheory_Kernel_nonempty_of_isMarkovKernel
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
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]
  [Countable V] [MeasurableSingletonClass V]
namespace ProbabilityTheory.Kernel
namespace _root_.ProbabilityTheory.Kernel
theorem _root_.solution
    {ξ : Kernel T S} [IsZeroOrMarkovKernel ξ]
    {κ : Kernel (T × S) U} [IsZeroOrMarkovKernel κ] {η :
      Kernel (T × S × U) V} [IsMarkovKernel η]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ (μ ⊗ₘ ξ))
    (hη : AEFiniteKernelSupport η (μ ⊗ₘ (ξ ⊗ₖ κ))) (hξ :
      AEFiniteKernelSupport ξ μ) :
    Hk[η, μ ⊗ₘ (ξ ⊗ₖ κ)]
      ≤ Hk[snd (κ ⊗ₖ (comap η MeasurableEquiv.prodAssoc
        MeasurableEquiv.prodAssoc.measurable)),
            μ ⊗ₘ ξ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rcases eq_zero_or_isMarkovKernel ξ with rfl | hξ'
  · simp
  have : Nonempty S := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ ξ
  have : Nonempty T := μ.nonempty_of_neZero
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  have : Nonempty U := nonempty_of_isMarkovKernel κ
  rcases eq_zero_or_isMarkovKernel η with rfl | hκ'
  · simp
  have : Nonempty V := nonempty_of_isMarkovKernel η
  have h_meas := (MeasurableEquiv.prodAssoc.symm : T × S × U ≃ᵐ (T × S) × U).symm.measurable
  have : FiniteSupport (μ ⊗ₘ ξ) := finiteSupport_of_compProd hξ
  have : FiniteSupport (μ ⊗ₘ (ξ ⊗ₖ κ)) := finiteSupport_of_compProd (hξ.compProd hκ)
  let η' : Kernel ((T × S) × U) V :=
    comap η MeasurableEquiv.prodAssoc h_meas
  let : IsMarkovKernel η' := IsMarkovKernel.comap η h_meas
  let : IsZeroOrMarkovKernel (κ ⊗ₖ η') :=
    IsZeroOrMarkovKernel.compProd κ η'
  have h := entropy_condKernel_le_entropy_snd
    (κ := κ ⊗ₖ η') (μ := μ ⊗ₘ ξ) ?_
  · simp only [fst_compProd] at h
    have : condKernel (κ ⊗ₖ η') =ᵐ[μ ⊗ₘ ξ ⊗ₘ κ] η' := by
      exact condKernel_compProd_ae_eq κ η' (μ ⊗ₘ ξ)
    dsimp only [η'] at h ⊢
    rwa [entropy_congr this, Measure.compProd_compProd'', entropy_comap_equiv] at h
  · refine (hκ.compProd ?_)
    convert hη.comap_equiv MeasurableEquiv.prodAssoc
    exact Measure.compProd_compProd'' _ _ _
end _root_.ProbabilityTheory.Kernel
end ProbabilityTheory.Kernel
