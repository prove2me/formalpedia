-- Prove2me | solution 1 for ZhangYeung.entropyFn_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:08:52.154798+00:00
-- url     : https://prove2.me/submissions/ab32ac72-4619-434f-8f0e-30ffbd3d7adb

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



set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology ZhangYeungPFR
universe u
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Fin 4 → Type u}
  [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
  [∀ i, MeasurableSingletonClass (S i)]
  (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) [IsProbabilityMeasure μ]
omit [IsProbabilityMeasure μ]
namespace ZhangYeung
theorem _root_.solution (hX : ∀ i, Measurable (X i))
    {i j : Fin 4} (h : i ≠ j) :
    entropyFn X μ {i, j} = H[⟨X i, X j⟩; μ] := by
  let : ∀ i, Fintype (S i) := fun i => Fintype.ofFinite (S i)
  simp only [entropyFn, entropyFnN]
  -- Projection π : (∀ k : {i, j}, S k.1) → S i × S j evaluating at both indices.
  have hi : i ∈ ({i, j} : Finset (Fin 4)) := by simp
  have hj : j ∈ ({i, j} : Finset (Fin 4)) := by simp
  let π : (∀ k : ({i, j} : Finset (Fin 4)), S k.1) → S i × S j :=
    fun g => (g ⟨i, hi⟩, g ⟨j, hj⟩)
  -- Injectivity: every k : {i, j} satisfies k.1 = i ∨ k.1 = j.
  have hπ : Function.Injective π := by
    intro g₁ g₂ heq
    have h₁ : g₁ ⟨i, hi⟩ = g₂ ⟨i, hi⟩ := (Prod.mk.inj heq).1
    have h₂ : g₁ ⟨j, hj⟩ = g₂ ⟨j, hj⟩ := (Prod.mk.inj heq).2
    funext k
    obtain ⟨k, hk⟩ := k
    rcases Finset.mem_insert.mp hk with hki | hk'
    · subst hki; exact h₁
    · have : k = j := Finset.mem_singleton.mp hk'
      subst this; exact h₂
  have h_meas : Measurable
      (fun ω : Ω => fun k : ({i, j} : Finset (Fin 4)) => X k.1 ω) :=
    measurable_pi_lambda _ (fun k => hX k.1)
  -- π ∘ joint = ⟨X i, X j⟩ definitionally.
  exact (entropy_comp_of_injective μ h_meas π hπ).symm
end ZhangYeung
