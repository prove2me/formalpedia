-- Prove2me | solution 1 for P2M_ProbabilityTheory_Kernel_entropy_triple_add_entropy_le__04a239f82394
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:04:38.900529+00:00
-- url     : https://prove2.me/submissions/7d3d119a-4376-4fa6-bd42-2043ee4d47e8

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Theorems.Thm_P2M_ProbabilityTheory_Kernel_compProd_assoc__371caf64c88a
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_triple_add_entropy_le
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_snd
public import Theorems.Thm_ProbabilityTheory_Kernel_aefiniteKernelSupport_of_cond
public import Theorems.Thm_ProbabilityTheory_Kernel_disintegration
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_map_of_injective
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prod
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
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
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]
  [Countable V] [MeasurableSingletonClass V]
namespace ProbabilityTheory.Kernel
namespace _root_.ProbabilityTheory.Kernel
theorem _root_.solution
    {κ : Kernel T (S × U × V)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[κ, μ] + Hk[fst κ, μ] ≤ Hk[deleteMiddle κ, μ] + Hk[deleteRight κ, μ] := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty (S × U × V) := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ κ
  inhabit (S × U × V)
  have : Nonempty U := ⟨(default : S × U × V).2.1⟩
  have : Nonempty V := ⟨(default : S × U × V).2.2⟩
  set κ' := map κ MeasurableEquiv.prodAssoc.symm with hκ'_def
  set ξ := fst (fst κ') with ξ_def
  let κ'' := condKernel (fst κ')
  let η := condKernel κ'
  have hξ_eq : ξ = fst κ := by
    rw [ξ_def, hκ'_def, fst_eq, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk,
      Equiv.coe_fn_mk,
     fst_eq, map_map _ (by fun_prop) (by fun_prop), map_map _ (by fun_prop) (by fun_prop), fst_eq]
    rfl
  have h_compProd_eq : ξ ⊗ₖ κ'' = fst κ' := (disintegration (fst κ')).symm
  have h_compProd_triple_eq : (ξ ⊗ₖ κ'') ⊗ₖ η = κ' := by
    rw [h_compProd_eq]
    exact (disintegration κ').symm
  have h_compProd_triple_eq' :
      ξ ⊗ₖ (κ'' ⊗ₖ comap η MeasurableEquiv.prodAssoc
        MeasurableEquiv.prodAssoc.measurable)
        = κ := by
    rw [← compProd_assoc', h_compProd_triple_eq,hκ'_def, map_map _ (by fun_prop) (by fun_prop)]
    simp
  have h := entropy_compProd_triple_add_entropy_le (ξ := ξ) (κ := κ'') (η := η) (μ :=
    μ) ?_ ?_ ?_
  rotate_left
  · exact aefiniteKernelSupport_of_cond _ hκ.map.fst
  · rw [h_compProd_eq]
    apply aefiniteKernelSupport_of_cond
    exact hκ.map
  · exact hκ.map.fst.fst
  rw [← hξ_eq]
  have h_right : deleteRight κ = fst κ' := by
    rw [hκ'_def, deleteRight_eq, fst_eq, map_map _ (by fun_prop) (by fun_prop)]
    congr
  have h_middle : deleteMiddle κ
      = ξ ⊗ₖ snd
        (κ'' ⊗ₖ comap η MeasurableEquiv.prodAssoc MeasurableEquiv.prodAssoc.measurable) := by
    rw [← deleteMiddle_compProd, h_compProd_triple_eq']
  have hκ : Hk[κ, μ] = Hk[κ', μ] := by
    rw [hκ'_def, entropy_map_of_injective _ _ _ (by fun_prop)]
    exact MeasurableEquiv.prodAssoc.symm.injective
  simp_all
end _root_.ProbabilityTheory.Kernel
end ProbabilityTheory.Kernel
