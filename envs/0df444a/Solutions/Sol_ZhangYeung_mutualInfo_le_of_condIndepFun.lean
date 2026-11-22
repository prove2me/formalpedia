-- Prove2me | solution 1 for ZhangYeung.mutualInfo_le_of_condIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:11:21.355544+00:00
-- url     : https://prove2.me/submissions/606d9758-305f-4d30-92dc-e75593108687

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_P2M_ProbabilityTheory_Kernel_chain_rule__5854b667e2d9
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prod
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_triple_add_entropy_le
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_kernel
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
public import Theorems.Thm_ProbabilityTheory_Kernel_mutualInfo_def
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteMiddle_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteRight_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_snd_reverse
public import Theorems.Thm_ProbabilityTheory_condEntropy_comm
public import Theorems.Thm_ProbabilityTheory_ent_of_cond_indep
public import Theorems.Thm_ProbabilityTheory_entropy_triple_add_entropy_le
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
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
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
open ZhangYeung
namespace ZhangYeung
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω]
    {α β γ : Type*}
    [Finite α] [Finite β] [Finite γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : CondIndepFun X Y Z μ) :
    I[X : Y; μ] ≤ I[X : Z; μ] := by
  have h_ent : H[⟨X, ⟨Y, Z⟩⟩; μ] = H[⟨X, Z⟩; μ] + H[⟨Y, Z⟩; μ] - H[Z; μ] :=
    ent_of_cond_indep μ hX hY hZ h
  have h_sub : H[⟨X, ⟨Z, Y⟩⟩; μ] + H[Y; μ] ≤ H[⟨X, Y⟩; μ] + H[⟨Z, Y⟩; μ] :=
    entropy_triple_add_entropy_le μ hX hZ hY
  have e_inner : H[⟨X, ⟨Z, Y⟩⟩; μ] = H[⟨X, ⟨Y, Z⟩⟩; μ] := by
    rw [chain_rule' μ hX (hZ.prodMk hY), chain_rule' μ hX (hY.prodMk hZ),
        condEntropy_comm hZ hY]
  have e_ZY : H[⟨Z, Y⟩; μ] = H[⟨Y, Z⟩; μ] := entropy_comm hZ hY μ
  simp only [mutualInfo_def]
  linarith [h_ent, h_sub, e_inner, e_ZY]
end ZhangYeung
