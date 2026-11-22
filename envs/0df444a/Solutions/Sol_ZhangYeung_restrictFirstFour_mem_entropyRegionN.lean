-- Prove2me | solution 1 for ZhangYeung.restrictFirstFour_mem_entropyRegionN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:09:05.693096+00:00
-- url     : https://prove2.me/submissions/96b5638c-fc12-4057-aac5-0b10d9f924aa

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Theorems.Thm_ZhangYeung_entropyFnN_restrictFirstFour
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
open scoped Topology
universe u
namespace ZhangYeung
theorem _root_.solution
    {n : ℕ} (hn : 4 ≤ n) {F : Finset (Fin n) → ℝ}
    (hF : F ∈ entropyRegionN.{u} n) :
    restrictFirstFour hn F ∈ entropyRegionN.{u} 4 := by
  rcases hF with ⟨Ω, hΩ, μ, hμ, S, hS, hFin, hMSC, X, hX, rfl⟩
  let : MeasurableSpace Ω := hΩ
  let : IsProbabilityMeasure μ := hμ
  let : ∀ i, MeasurableSpace (S i) := hS
  let : ∀ i, Fintype (S i) := hFin
  let : ∀ i, MeasurableSingletonClass (S i) := hMSC
  refine ⟨Ω, inferInstance, μ, inferInstance, (fun i : Fin 4 => S (Fin.castLE hn i)),
    inferInstance,
    inferInstance, inferInstance, (fun i : Fin 4 => X (Fin.castLE hn i)),
    fun i => hX (Fin.castLE hn i), ?_⟩
  simpa using entropyFnN_restrictFirstFour hX μ hn
end ZhangYeung
