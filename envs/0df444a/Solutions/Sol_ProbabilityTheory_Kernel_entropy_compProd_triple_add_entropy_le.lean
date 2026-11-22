-- Prove2me | solution 1 for ProbabilityTheory.Kernel.entropy_compProd_triple_add_entropy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:03:32.495926+00:00
-- url     : https://prove2.me/submissions/c958f784-0b0a-4584-ab3d-c91433453763

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Theorems.Thm_P2M_ProbabilityTheory_Kernel_Measure_compProd_compProd___39a21c44794a
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_condKernel_compProd_triple
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_submodular_compProd
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_comap_equiv
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_compProd
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_snd
public import Theorems.Thm_ProbabilityTheory_Kernel_FiniteKernelSupport_compProd
public import Theorems.Thm_ProbabilityTheory_Kernel_FiniteSupport_comap_equiv
public import Theorems.Thm_ProbabilityTheory_Kernel_chain_rule
public import Theorems.Thm_ProbabilityTheory_Kernel_condKernel_compProd_ae_eq
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_congr
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prod
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_kernel
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
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
    {κ : Kernel (T × S) U} [IsMarkovKernel κ]
    {η : Kernel (T × S × U) V} [IsMarkovKernel η]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ (μ ⊗ₘ ξ))
    (hη : AEFiniteKernelSupport η (μ ⊗ₘ (ξ ⊗ₖ κ))) (hξ :
      AEFiniteKernelSupport ξ μ) :
    Hk[(ξ ⊗ₖ κ) ⊗ₖ η, μ] + Hk[ξ, μ]
      ≤ Hk[ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc
        MeasurableEquiv.prodAssoc.measurable),
          μ] + Hk[ξ ⊗ₖ κ, μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rcases eq_zero_or_isMarkovKernel ξ with rfl | hξ'
  · simp
  have : Nonempty S := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ ξ
  have : Nonempty T := μ.nonempty_of_neZero
  have : Nonempty U := nonempty_of_isMarkovKernel κ
  have : Nonempty V := nonempty_of_isMarkovKernel η
  rw [chain_rule, chain_rule (κ := ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc
    MeasurableEquiv.prodAssoc.measurable))]
  · simp only [fst_compProd, entropy_condKernel_compProd_triple]
    calc Hk[ξ ⊗ₖ κ , μ] + Hk[η , μ ⊗ₘ (ξ ⊗ₖ κ)] + Hk[ξ , μ]
      = Hk[ξ , μ] + Hk[ξ ⊗ₖ κ , μ] + Hk[η , μ ⊗ₘ (ξ ⊗ₖ κ)] := by abel
    _ ≤ Hk[ξ , μ] + Hk[ξ ⊗ₖ κ , μ]
      + Hk[condKernel (ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc _)) ,
        μ ⊗ₘ ξ] := by
        refine add_le_add le_rfl ?_
        refine (entropy_submodular_compProd hκ hη hξ).trans_eq ?_
        refine entropy_congr ?_
        exact (condKernel_compProd_ae_eq _ _ _).symm
    _ = Hk[ξ ,
      μ] + Hk[condKernel (ξ ⊗ₖ snd (κ ⊗ₖ comap η MeasurableEquiv.prodAssoc _)),
      μ ⊗ₘ ξ] +
          Hk[ξ ⊗ₖ κ , μ] := by abel
  · refine hξ.compProd ?_
    refine AEFiniteKernelSupport.snd ?_
    refine hκ.compProd ?_
    convert hη.comap_equiv MeasurableEquiv.prodAssoc
    exact Measure.compProd_compProd'' _ _ _
  · exact (hξ.compProd hκ).compProd hη
end _root_.ProbabilityTheory.Kernel
end ProbabilityTheory.Kernel
