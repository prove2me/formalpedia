-- Prove2me | solution 1 for ZhangYeung.not_zhangYeungHolds_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:56:05.419495+00:00
-- url     : https://prove2.me/submissions/4d611a6d-415f-4b47-b130-4c43bbbfbb76

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4
public import Theorems.Thm_ZhangYeung_FWitness_eq_cast
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
private lemma not_zhangYeungAt_witness_canonical :
    ¬ zhangYeungAt FWitness 2 3 0 1 := by
  intro h
  simp only [zhangYeungAt, deltaF, IF, condIF, FWitness_eq_cast] at h
  have h00 : FWitnessℚ ({0} : Finset (Fin 4)) = 2 := by decide
  have h11 : FWitnessℚ ({1} : Finset (Fin 4)) = 2 := by decide
  have h22 : FWitnessℚ ({2} : Finset (Fin 4)) = 2 := by decide
  have h33 : FWitnessℚ ({3} : Finset (Fin 4)) = 2 := by decide
  have h01 : FWitnessℚ (({0} : Finset (Fin 4)) ∪ {1}) = 4 := by decide
  have h02 : FWitnessℚ (({2} : Finset (Fin 4)) ∪ {0}) = 3 := by decide
  have h03 : FWitnessℚ (({3} : Finset (Fin 4)) ∪ {0}) = 3 := by decide
  have h12 : FWitnessℚ (({2} : Finset (Fin 4)) ∪ {1}) = 3 := by decide
  have h13 : FWitnessℚ (({3} : Finset (Fin 4)) ∪ {1}) = 3 := by decide
  have h23 : FWitnessℚ (({2} : Finset (Fin 4)) ∪ {3}) = 3 := by decide
  have h023 : FWitnessℚ (({2} : Finset (Fin 4)) ∪ {3} ∪ {0}) = 4 := by decide
  have h123 : FWitnessℚ (({2} : Finset (Fin 4)) ∪ {3} ∪ {1}) = 4 := by decide
  have h023' : FWitnessℚ (({0} : Finset (Fin 4)) ∪ (({2} : Finset (Fin 4)) ∪ {3})) = 4 := by
    decide
  rw [h00, h11, h22, h33, h01, h02, h03, h12, h13, h23, h023, h123, h023'] at h
  norm_num at h
section EntropyFnEvaluation
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Fin 4 → Type u}
  [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
  [∀ i, MeasurableSingletonClass (S i)]
  (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) [IsProbabilityMeasure μ]
end EntropyFnEvaluation
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
theorem _root_.solution : ¬ zhangYeungHolds FWitness := by
  intro h
  specialize h (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3)
  rw [show (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 0 = 2 from by decide,
      show (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 = 3 from by decide,
      show (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 2 = 0 from by decide,
      show (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 3 = 1 from by decide] at h
  exact not_zhangYeungAt_witness_canonical h
end ZhangYeung
