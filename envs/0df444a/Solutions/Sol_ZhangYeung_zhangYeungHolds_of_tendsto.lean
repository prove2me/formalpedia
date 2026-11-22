-- Prove2me | solution 1 for ZhangYeung.zhangYeungHolds_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:01:59.245228+00:00
-- url     : https://prove2.me/submissions/c2633b97-7ebd-4cac-bddb-795d5842fc2a

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
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


section
@[expose] public section
namespace ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology ZhangYeungPFR
universe u
section EntropyFnEvaluation
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Fin 4 → Type u}
  [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
  [∀ i, MeasurableSingletonClass (S i)]
  (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) [IsProbabilityMeasure μ]
end EntropyFnEvaluation
private lemma IF_tendsto
    {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α)))
    (α β : Finset (Fin 4)) :
    Filter.Tendsto (fun k => IF (F_seq k) α β) Filter.atTop (𝓝 (IF F α β)) := by
  simp only [IF]
  exact ((h α).add (h β)).sub (h _)
private lemma condIF_tendsto
    {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α)))
    (α β γ : Finset (Fin 4)) :
    Filter.Tendsto (fun k => condIF (F_seq k) α β γ) Filter.atTop (𝓝 (condIF F α β
      γ)) := by
  simp only [condIF]
  exact (((h _).add (h _)).sub (h _)).sub (h _)
private lemma deltaF_tendsto
    {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α)))
    (i j k l : Fin 4) :
    Filter.Tendsto (fun n => deltaF (F_seq n) i j k l) Filter.atTop
      (𝓝 (deltaF F i j k l)) := by
  simp only [deltaF]
  exact ((IF_tendsto h _ _).sub (condIF_tendsto h _ _ _)).sub (condIF_tendsto h _ _ _)
end ZhangYeung
end
end

set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology ZhangYeungPFR
universe u
namespace ZhangYeung
namespace _root_.ZhangYeung
theorem _root_.solution
    {F_seq : ℕ → Finset (Fin 4) → ℝ} {F : Finset (Fin 4) → ℝ}
    (h_seq : ∀ k, zhangYeungHolds (F_seq k))
    (h_lim : ∀ α, Filter.Tendsto (fun k => F_seq k α) Filter.atTop (𝓝 (F α))) :
    zhangYeungHolds F := by
  intro π
  have h_LHS := deltaF_tendsto h_lim (π 0) (π 1) (π 2) (π 3)
  have h_RHS :
      Filter.Tendsto
        (fun k => (1 / 2 : ℝ) * (IF (F_seq k) {π 2} {π 3}
              + IF (F_seq k) {π 2} ({π 0} ∪ {π 1})
              + condIF (F_seq k) {π 0} {π 1} {π 2}
              - condIF (F_seq k) {π 0} {π 1} {π 3}))
        Filter.atTop
        (𝓝 ((1 / 2 : ℝ) * (IF F {π 2} {π 3}
            + IF F {π 2} ({π 0} ∪ {π 1})
            + condIF F {π 0} {π 1} {π 2}
            - condIF F {π 0} {π 1} {π 3}))) := by
    refine Filter.Tendsto.const_mul _ ?_
    exact (((IF_tendsto h_lim _ _).add (IF_tendsto h_lim _ _)).add
      (condIF_tendsto h_lim _ _ _)).sub (condIF_tendsto h_lim _ _ _)
  exact le_of_tendsto_of_tendsto' h_LHS h_RHS (fun k => h_seq k π)
end _root_.ZhangYeung
end ZhangYeung
