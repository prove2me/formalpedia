-- Prove2me | solution 1 for ProbabilityTheory.condEntropy_prod_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:04:13.627799+00:00
-- url     : https://prove2.me/submissions/b7204f4d-c706-4843-a29c-f804d42f6296

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_condEntropy_eq_sum_fintype
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prod
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_kernel
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteMiddle_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteRight_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_snd_reverse
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
public import Theorems.Thm_ZhangYeungImport_ProbabilityTheory_cond_real_apply
public import Theorems.Thm_prod_eq
attribute [local simp] MeasureTheory.Measure.pi_eval_preimage
attribute [local simp] MeasureTheory.Measure.pi_pi_set
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
attribute [local simp] ProbabilityTheory.identDistrib_id
attribute [local simp] ProbabilityTheory.indepFun_zero_measure
attribute [local simp] prod_eq



set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
variable [MeasurableSpace T]
variable {X : Ω → S} {Y : Ω → T}
variable [MeasurableSingletonClass T]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution
    {X : Ω → S} {Y : Ω → T} {Z : Ω → T'} [MeasurableSpace T']
    [MeasurableSingletonClass T']
    (μ : Measure Ω) (hY : Measurable Y) (hZ : Measurable Z)
    [IsFiniteMeasure μ] [Finite T] [Fintype T'] :
    H[X | ⟨Y, Z⟩; μ] = ∑ z, μ.real (Z ⁻¹' {z}) * H[X | Y; μ[|Z ⁻¹' {z}]] := by
  cases nonempty_fintype T
  simp_rw [condEntropy_eq_sum_fintype _ _ _ (hY.prodMk hZ), condEntropy_eq_sum_fintype _ _ _ hY,
    Fintype.sum_prod_type_right, Finset.mul_sum, ← mul_assoc]
  congr with y
  congr with x
  have A : (fun a ↦ (Y a, Z a)) ⁻¹' {(x, y)} = Z ⁻¹' {y} ∩ Y ⁻¹' {x} := by
    ext p; simp [and_comm]
  congr 2
  · rw [cond_real_apply (hZ (.singleton y)), A]
    obtain hy | hy := eq_or_ne (μ.real (Z ⁻¹' {y})) 0
    · have : μ.real (Z ⁻¹' {y} ∩ Y ⁻¹' {x}) = 0 :=
        measureReal_mono_null Set.inter_subset_left hy (by finiteness)
      simp [this, hy]
    · rw [mul_inv_cancel_left₀ hy]
  · rw [A, cond_cond_eq_cond_inter (hZ (.singleton y)) (hY (.singleton x))]
end _root_.ProbabilityTheory
end ProbabilityTheory
