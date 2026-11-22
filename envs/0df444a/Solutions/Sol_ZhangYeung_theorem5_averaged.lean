-- Prove2me | solution 1 for ZhangYeung.theorem5_averaged
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:15:54.842672+00:00
-- url     : https://prove2.me/submissions/a43a57a6-4ee2-4435-8639-f4d29f6d9c28

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem5
public import Theorems.Thm_ZhangYeung_theorem5
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
open scoped ZhangYeungPFR
universe u
variable {Ω : Type*} [MeasurableSpace Ω]
  {n : ℕ}
  {S_U S_Z : Type u} {S : Fin n → Type u}
  [MeasurableSpace S_U] [MeasurableSpace S_Z]
  [∀ i, MeasurableSpace (S i)]
  [Finite S_U] [Finite S_Z] [∀ i, Finite (S i)]
  [MeasurableSingletonClass S_U] [MeasurableSingletonClass S_Z]
  [∀ i, MeasurableSingletonClass (S i)]
namespace ZhangYeung
namespace _root_.ZhangYeung
theorem _root_.solution
    (hn : 2 ≤ n)
    {U : Ω → S_U} {Z : Ω → S_Z} {X : ∀ i : Fin n, Ω → S i}
    (hU : Measurable U) (hZ : Measurable Z) (hX : ∀ i, Measurable (X i))
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    n * I[U : Z; μ] - 2 * (∑ j, I[U : Z | X j; μ])
      ≤ (1 / n : ℝ) * (∑ i, I[X i : ⟨U, Z⟩; μ])
        + ∑ j, H[X j; μ]
        - H[(fun ω : Ω => fun j : Fin n => X j ω); μ] := by
  let lhs : ℝ := n * I[U : Z; μ] - 2 * (∑ j : Fin n, I[U : Z | X j; μ])
  let tail : ℝ := ∑ j : Fin n, H[X j; μ] - H[(fun ω : Ω => fun j : Fin n => X j ω); μ]
  let rhs : Fin n → ℝ := fun i => I[X i : ⟨U, Z⟩; μ]
  have hsum : ∑ i : Fin n, (n * I[U : Z; μ] - ∑ j : Fin n,
    I[U : Z | X j; μ] - n * I[U : Z | X i; μ])
      ≤ ∑ i : Fin n, (rhs i + tail) := by
    refine Finset.sum_le_sum ?_
    intro i _
    simpa [rhs, tail, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (theorem5 hU hZ hX μ i hn)
  have hleft :
      ∑ i : Fin n, (n * I[U : Z; μ] - ∑ j : Fin n, I[U : Z | X j; μ] - n * I[U : Z | X i; μ])
        = n * lhs := by
    have hsumCond : ∑ x : Fin n, n * I[U : Z | X x; μ] = n * ∑ x : Fin n,
      I[U : Z | X x; μ] := by
      rw [Finset.mul_sum]
    calc
      ∑ i : Fin n, (n * I[U : Z; μ] - ∑ j : Fin n, I[U : Z | X j; μ] - n * I[U : Z | X i; μ])
          = n ^ 2 * I[U : Z; μ] - ∑ x : Fin n, n * I[U : Z | X x; μ] - n * ∑ j : Fin n,
            I[U : Z | X j; μ] := by
            simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            ring
      _ = n ^ 2 * I[U : Z; μ] - n * ∑ x : Fin n, I[U : Z | X x; μ] - n * ∑ j : Fin n,
        I[U : Z | X j; μ] := by
            rw [hsumCond]
      _ = n * lhs := by
            change n ^ 2 * I[U : Z; μ] - n * ∑ x : Fin n,
              I[U : Z | X x; μ] - n * ∑ j : Fin n, I[U : Z | X j; μ]
              = n * (n * I[U : Z; μ] - 2 * ∑ j : Fin n, I[U : Z | X j; μ])
            ring
  have hright : ∑ i : Fin n, (rhs i + tail) = (∑ i : Fin n, rhs i) + n * tail := by
    simp only [rhs, tail, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin,
      nsmul_eq_mul]
  have hscaled : n * lhs ≤ (∑ i : Fin n, rhs i) + n * tail := by
    simpa [hleft, hright] using hsum
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hdiv : lhs ≤ ((∑ i : Fin n, rhs i) + n * tail) / n :=
    (le_div_iff₀ hn_pos).2 (by simpa [mul_comm] using hscaled)
  have hsplit : ((∑ i : Fin n, rhs i) + n * tail) / n = (1 / n : ℝ) * (∑ i : Fin n,
    rhs i) + tail := by
    field_simp [hn_ne]
  rw [hsplit] at hdiv
  simpa [lhs, rhs, tail, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using hdiv
end _root_.ZhangYeung
end ZhangYeung
