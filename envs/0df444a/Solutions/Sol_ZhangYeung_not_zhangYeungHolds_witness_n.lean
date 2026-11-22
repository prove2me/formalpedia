-- Prove2me | solution 1 for ZhangYeung.not_zhangYeungHolds_witness_n
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:02:08.045715+00:00
-- url     : https://prove2.me/submissions/d02121d9-d01d-4d28-9caa-1407513d21bd

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
private lemma preimage_singleton_castLE {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) :
    ({Fin.castLE hn i} : Finset (Fin n)).preimage (Fin.castLE hn)
        (Fin.castLE_injective hn).injOn = ({i} : Finset (Fin 4)) := by
  ext j
  simp_all
private lemma preimage_pair_castLE {n : ℕ} (hn : 4 ≤ n) (i j : Fin 4) :
    (({Fin.castLE hn i} : Finset (Fin n)) ∪ {Fin.castLE hn j}).preimage
        (Fin.castLE hn) (Fin.castLE_injective hn).injOn =
      ({i} : Finset (Fin 4)) ∪ {j} := by
  rw [Finset.preimage_union, preimage_singleton_castLE, preimage_singleton_castLE]
private lemma zhangYeungAtN_witness_castLE {n : ℕ} (hn : 4 ≤ n) (i j k l : Fin 4) :
    zhangYeungAtN (FWitnessN hn) (Fin.castLE hn i) (Fin.castLE hn j)
        (Fin.castLE hn k) (Fin.castLE hn l)
      ↔ zhangYeungAt FWitness i j k l := by
  unfold zhangYeungAtN zhangYeungAt deltaFN deltaF IFN IF condIFN condIF FWitnessN
  simp only [Finset.preimage_union, preimage_singleton_castLE, preimage_pair_castLE]
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
theorem _root_.solution {n : ℕ} (hn : 4 ≤ n) :
    ¬ zhangYeungHoldsN (FWitnessN hn) := by
  intro h
  have inj := Fin.castLE_injective hn
  have d : ∀ a b : Fin 4, a ≠ b → (Fin.castLE hn a : Fin n) ≠ Fin.castLE hn b :=
    fun _ _ hab e => hab (inj e)
  have hat := h (Fin.castLE hn 2) (Fin.castLE hn 3) (Fin.castLE hn 0) (Fin.castLE hn 1)
    (d 2 3 (by decide)) (d 2 0 (by decide)) (d 2 1 (by decide))
    (d 3 0 (by decide)) (d 3 1 (by decide)) (d 0 1 (by decide))
  exact not_zhangYeungAt_witness_canonical ((zhangYeungAtN_witness_castLE hn 2 3 0 1).mp hat)
end _root_.ZhangYeung
end ZhangYeung
