-- Prove2me | solution 1 for ZhangYeung.theorem4_ge_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:20:30.189745+00:00
-- url     : https://prove2.me/submissions/af203451-389a-4dfa-8379-0d5ce599a8a1

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4
public import Theorems.Thm_ZhangYeung_not_zhangYeungHolds_witness
public import Theorems.Thm_ZhangYeung_zhangYeungHolds_of_entropy
public import Theorems.Thm_ZhangYeung_shannonCone_of_witness_n
public import Theorems.Thm_ZhangYeung_restrictFirstFour_witness_n
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_mul
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
public import Theorems.Thm_ZhangYeung_restrictFirstFour_mem_almostEntropicRegionN
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
private lemma continuous_IF (α β : Finset (Fin 4)) :
    Continuous (fun F : Finset (Fin 4) → ℝ => IF F α β) := by
  unfold IF
  apply (((continuous_apply α).add (continuous_apply β)).sub
    (continuous_apply (α ∪ β))).congr
  intro F
  rfl
private lemma continuous_condIF (α β γ : Finset (Fin 4)) :
    Continuous (fun F : Finset (Fin 4) → ℝ => condIF F α β γ) := by
  unfold condIF
  apply ((((continuous_apply (α ∪ γ)).add (continuous_apply (β ∪ γ))).sub
    (continuous_apply (α ∪ (β ∪ γ)))).sub (continuous_apply γ)).congr
  intro F
  simp only [Pi.add_apply, Pi.sub_apply, ← Finset.union_assoc]
private lemma continuous_deltaF (i j k l : Fin 4) :
    Continuous (fun F : Finset (Fin 4) → ℝ => deltaF F i j k l) := by
  unfold deltaF
  apply (((continuous_IF {i} {j}).sub (continuous_condIF {i} {j} {k})).sub
    (continuous_condIF {i} {j} {l})).congr
  intro F
  rfl
private lemma isClosed_zhangYeungAt_set (π : Equiv.Perm (Fin 4)) :
    IsClosed {F : Finset (Fin 4) → ℝ | zhangYeungAt F (π 0) (π 1) (π 2) (π 3)} := by
  unfold zhangYeungAt
  refine isClosed_le (continuous_deltaF _ _ _ _) ?_
  refine continuous_const.mul ?_
  exact (((continuous_IF {π 2} {π 3}).add (continuous_IF {π 2} ({π 0} ∪ {π 1}))).add
    (continuous_condIF {π 0} {π 1} {π 2})).sub (continuous_condIF {π 0} {π 1} {π 3})
private lemma isClosed_zhangYeungRegion_4 : IsClosed zhangYeungRegion_4 := by
  classical
  have h_eq : zhangYeungRegion_4 =
      ⋂ π : Equiv.Perm (Fin 4),
        {F : Finset (Fin 4) → ℝ | zhangYeungAt F (π 0) (π 1) (π 2) (π 3)} := by
    ext F
    simp [zhangYeungRegion_4, zhangYeungHolds]
  rw [h_eq]
  exact isClosed_iInter fun π : Equiv.Perm (Fin 4) => isClosed_zhangYeungAt_set π
private lemma entropyRegion_four_subset_zhangYeungRegion_4 :
    entropyRegionN.{u} 4 ⊆ zhangYeungRegion_4 := by
  intro F hF
  rcases hF with ⟨Ω, hΩ, μ, hμ, S, hS, hFin, hMSC, X, hX, h_eq⟩
  let : MeasurableSpace Ω := hΩ
  let : IsProbabilityMeasure μ := hμ
  let : ∀ i, MeasurableSpace (S i) := hS
  let : ∀ i, Fintype (S i) := hFin
  let : ∀ i, MeasurableSingletonClass (S i) := hMSC
  rw [h_eq]
  simpa [zhangYeungRegion_4] using zhangYeungHolds_of_entropy hX μ
private lemma almostEntropicRegion_four_subset_zhangYeungRegion_4 :
    almostEntropicRegionN.{u} 4 ⊆ zhangYeungRegion_4 := by
  simpa [almostEntropicRegionN] using
    (closure_minimal entropyRegion_four_subset_zhangYeungRegion_4 isClosed_zhangYeungRegion_4)
private lemma not_mem_almostEntropicRegion_witness :
    FWitness ∉ almostEntropicRegionN.{u} 4 := fun hF =>
  not_zhangYeungHolds_witness (almostEntropicRegion_four_subset_zhangYeungRegion_4 hF)
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
theorem _root_.solution (n : ℕ) (hn : 4 ≤ n) :
    ∃ F : Finset (Fin n) → ℝ,
      F ∈ shannonRegionN n ∧ F ∉ almostEntropicRegionN.{u} n := by
  refine ⟨FWitnessN hn, shannonCone_of_witness_n hn, ?_⟩
  · intro hF
    have h_restrict : FWitness ∈ almostEntropicRegionN.{u} 4 := by
      simpa [restrictFirstFour_witness_n hn] using restrictFirstFour_mem_almostEntropicRegionN
        hn hF
    exact not_mem_almostEntropicRegion_witness h_restrict
end _root_.ZhangYeung
end ZhangYeung
