-- Prove2me | solution 1 for ZhangYeung.zhangYeungAt_entropyFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:18:07.8223+00:00
-- url     : https://prove2.me/submissions/11a40655-0a4f-4f7a-aabd-db37f0219dbc

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4
public import Theorems.Thm_ZhangYeung_entropyFn_singleton
public import Theorems.Thm_ZhangYeung_entropyFn_pair
public import Theorems.Thm_ZhangYeung_entropyFn_triple
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_P2M_ProbabilityTheory_chain_rule___ff6bade4a15d
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prod
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_kernel
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
public import Theorems.Thm_ProbabilityTheory_Kernel_mutualInfo_def
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteMiddle_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteRight_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_snd_reverse
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_eq
public import Theorems.Thm_ProbabilityTheory_entropy_assoc
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
public import Theorems.Thm_ZhangYeung_IdentDistrib_condMutualInfo_eq
public import Theorems.Thm_ZhangYeung_delta_def
public import Theorems.Thm_ZhangYeung_zhangYeung
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
namespace ZhangYeung
namespace _root_.ZhangYeung
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω]
    {S : Fin 4 → Type u}
    [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
    [∀ i, MeasurableSingletonClass (S i)]
    {X : ∀ i : Fin 4, Ω → S i} (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (π : Equiv.Perm (Fin 4)) :
    zhangYeungAt (entropyFn X μ) (π 0) (π 1) (π 2) (π 3) := by
  -- Distinctness of the four permuted indices from injectivity of `π`.
  have d : ∀ a b : Fin 4, a ≠ b → π a ≠ π b := fun _ _ hab h => hab (π.injective h)
  have h01 : π 0 ≠ π 1 := d 0 1 (by decide)
  have h02 : π 0 ≠ π 2 := d 0 2 (by decide)
  have h03 : π 0 ≠ π 3 := d 0 3 (by decide)
  have h12 : π 1 ≠ π 2 := d 1 2 (by decide)
  have h13 : π 1 ≠ π 3 := d 1 3 (by decide)
  have h23 : π 2 ≠ π 3 := d 2 3 (by decide)
  -- Apply M3 at the labeling `(X_M3, Y_M3, Z_M3, U_M3) =
  -- (X (π 2), X (π 3), X (π 0), X (π 1))`.
  have hM3 := ZhangYeung.zhangYeung (hX (π 2)) (hX (π 3)) (hX (π 0)) (hX (π 1)) μ
  -- Fully unfold `hM3` into unconditional `H[_; μ]` arithmetic, matching the
  -- shape the set-function bridge produces.
  rw [delta_def, mutualInfo_def, mutualInfo_def, mutualInfo_def,
      condMutualInfo_eq (hX (π 0)) (hX (π 1)) (hX (π 2)) μ,
      condMutualInfo_eq (hX (π 0)) (hX (π 1)) (hX (π 3)) μ,
      chain_rule'' μ (hX (π 0)) (hX (π 2)),
      chain_rule'' μ (hX (π 1)) (hX (π 2)),
      chain_rule'' μ ((hX (π 0)).prodMk (hX (π 1))) (hX (π 2)),
      chain_rule'' μ (hX (π 0)) (hX (π 3)),
      chain_rule'' μ (hX (π 1)) (hX (π 3)),
      chain_rule'' μ ((hX (π 0)).prodMk (hX (π 1))) (hX (π 3)),
      ← entropy_assoc (hX (π 0)) (hX (π 1)) (hX (π 2)) μ,
      ← entropy_assoc (hX (π 0)) (hX (π 1)) (hX (π 3)) μ] at hM3
  -- Unfold the set-function calculus on the goal.
  unfold zhangYeungAt deltaF IF condIF
  -- Collapse `{x} ∪ s` and `insert a s ∪ t` to canonical `insert`-form so the
  -- `entropyFn_pair`/`entropyFn_triple` bridges fire without further massage.
  simp only [Finset.singleton_union, Finset.insert_union]
  -- Apply the per-subset bridge lemmas.
  rw [entropyFn_singleton X μ hX (π 0), entropyFn_singleton X μ hX (π 1),
      entropyFn_singleton X μ hX (π 2), entropyFn_singleton X μ hX (π 3),
      entropyFn_pair X μ hX h01, entropyFn_pair X μ hX h02,
      entropyFn_pair X μ hX h03, entropyFn_pair X μ hX h12,
      entropyFn_pair X μ hX h13, entropyFn_pair X μ hX h23,
      entropyFn_triple X μ hX h01 h02 h12,
      entropyFn_triple X μ hX h01 h03 h13,
      entropyFn_triple X μ hX h02.symm h12.symm h01]
  linarith
end _root_.ZhangYeung
end ZhangYeung
