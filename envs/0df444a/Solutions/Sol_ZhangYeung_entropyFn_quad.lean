-- Prove2me | solution 1 for ZhangYeung.entropyFn_quad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:15:51.685233+00:00
-- url     : https://prove2.me/submissions/24033970-0788-44a6-b2a1-6aff2b222517

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
theorem _root_.solution (hX : ∀ i, Measurable (X i)) :
    entropyFn X μ ({0, 1, 2, 3} : Finset (Fin 4))
      = H[⟨X 0, ⟨X 1, ⟨X 2, X 3⟩⟩⟩; μ] := by
  let : ∀ i, Fintype (S i) := fun i => Fintype.ofFinite (S i)
  simp only [entropyFn, entropyFnN]
  have h0 : (0 : Fin 4) ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  have h1 : (1 : Fin 4) ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  have h2 : (2 : Fin 4) ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  have h3 : (3 : Fin 4) ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  let π : (∀ m : ({0, 1, 2, 3} : Finset (Fin 4)), S m.1)
      → S 0 × (S 1 × (S 2 × S 3)) :=
    fun g => (g ⟨0, h0⟩, (g ⟨1, h1⟩, (g ⟨2, h2⟩, g ⟨3, h3⟩)))
  have hπ : Function.Injective π := by
    intro g₁ g₂ heq
    have e1 : g₁ ⟨0, h0⟩ = g₂ ⟨0, h0⟩ := (Prod.mk.inj heq).1
    have e2 : g₁ ⟨1, h1⟩ = g₂ ⟨1, h1⟩ := (Prod.mk.inj (Prod.mk.inj heq).2).1
    have e3 : g₁ ⟨2, h2⟩ = g₂ ⟨2, h2⟩ :=
      (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj heq).2).2).1
    have e4 : g₁ ⟨3, h3⟩ = g₂ ⟨3, h3⟩ :=
      (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj heq).2).2).2
    funext m
    obtain ⟨m, hm⟩ := m
    fin_cases m
    · exact e1
    · exact e2
    · exact e3
    · exact e4
  have h_meas : Measurable
      (fun ω : Ω => fun m : ({0, 1, 2, 3} : Finset (Fin 4)) => X m.1 ω) :=
    measurable_pi_lambda _ (fun m => hX m.1)
  exact (entropy_comp_of_injective μ h_meas π hπ).symm
end ZhangYeung
