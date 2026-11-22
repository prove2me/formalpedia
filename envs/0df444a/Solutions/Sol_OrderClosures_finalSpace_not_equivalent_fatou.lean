-- Prove2me | solution 1 for OrderClosures.finalSpace_not_equivalent_fatou
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:22:50.317772+00:00
-- url     : https://prove2.me/submissions/d150009a-6acd-420c-9e57-ca408786e779

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FinalSpace
public import Theorems.Thm_OrderClosures_finalLargeVector_properties
public import Theorems.Thm_LLexpr_NormalForm_eval_add
public import Theorems.Thm_LLexpr_NormalForm_eval_inf
public import Theorems.Thm_LLexpr_NormalForm_eval_negate
public import Theorems.Thm_LLexpr_NormalForm_eval_smul
public import Theorems.Thm_LLexpr_NormalForm_eval_sup
public import Theorems.Thm_LLexpr_NormalForm_eval_var
public import Theorems.Thm_LLexpr_NormalForm_eval_zero
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_add
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
public import Theorems.Thm_LLexpr_eval_add
public import Theorems.Thm_LLexpr_eval_inf
public import Theorems.Thm_LLexpr_eval_reindexExpr
public import Theorems.Thm_LLexpr_eval_smul
public import Theorems.Thm_LLexpr_eval_sup
public import Theorems.Thm_LLexpr_eval_var
public import Theorems.Thm_LLexpr_eval_zero
public import Theorems.Thm_LLexpr_normalize_eval
public import Theorems.Thm_OrderClosures_fatou_iterated_unitBall
public import Theorems.Thm_OrderClosures_iteratedOrderAdherence_mono_and_scale
public import Theorems.Thm_OrderClosures_orderAdherence_mono
public import Theorems.Thm_OrderConvergesTo_le
public import Theorems.Thm_OrderConvergesTo_smul
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
attribute [local simp] LLexpr.NormalForm.eval_add
attribute [local simp] LLexpr.NormalForm.eval_inf
attribute [local simp] LLexpr.NormalForm.eval_negate
attribute [local simp] LLexpr.NormalForm.eval_smul
attribute [local simp] LLexpr.NormalForm.eval_sup
attribute [local simp] LLexpr.NormalForm.eval_var
attribute [local simp] LLexpr.NormalForm.eval_zero
attribute [local simp] LLexpr.SupLinearCombination.eval_add
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
attribute [local simp] LLexpr.SupLinearCombination.eval_smul
attribute [local simp] LLexpr.SupLinearCombination.eval_sup
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.normalize_eval
attribute [local simp] Positive.extension_apply
attribute [local simp] VectorSublattice.coe_toSubmodule
attribute [local simp] VectorSublattice.mem_bot
attribute [local simp] VectorSublattice.mem_top
attribute [local simp] coe_toCompletionVecLatHom



set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution :
    ∀ q : PaperLatticeNorm FinalSpace,
      HasFatouProperty q → ¬ EquivalentNorms finalLatticeNorm q := by
  intro q hq hequiv
  rcases hequiv with ⟨c, C, hc, hC, hcompare⟩
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt (C / c : ℝ) (by norm_num : (1 : ℝ) < 2)
  let n := n₀ + 1
  have hn : 1 ≤ n := by simp [n]
  have hlarge : C < c * (2 : ℝ) ^ n := by
    have hpow : (2 : ℝ) ^ n₀ < (2 : ℝ) ^ n := by
      change (2 : ℝ) ^ n₀ < (2 : ℝ) ^ (n₀ + 1)
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n₀]
    have hcdiv : C < c * (2 : ℝ) ^ n₀ := by
      rw [div_lt_iff₀ hc] at hn₀
      simpa [mul_comm] using hn₀
    exact hcdiv.trans (mul_lt_mul_of_pos_left hpow hc)
  have hball : unitBallFor finalLatticeNorm ⊆ scaleSet C (unitBallFor q) := by
    intro z hz
    refine ⟨C⁻¹ • z, ?_, ?_⟩
    · change q (C⁻¹ • z) ≤ 1
      rw [q.smul, abs_of_pos (inv_pos.mpr hC), inv_mul_le_one₀ hC]
      exact (hcompare z).2.trans (by
        simpa using mul_le_mul_of_nonneg_left hz hC.le)
    · simp [smul_smul, hC.ne']
  have hitermono : ∀ k,
      iteratedOrderAdherence (unitBallFor finalLatticeNorm) k ⊆
        iteratedOrderAdherence (scaleSet C (unitBallFor q)) k := by
    intro k
    induction k with
    | zero => exact hball
    | succ k ih => exact orderAdherence_mono ih
  have hscale :=
    (iteratedOrderAdherence_mono_and_scale
      (A := unitBallFor q) (B := unitBallFor q) hC).2.2 n
  have hz := hitermono n (finalLargeVector_properties n).1
  rw [hscale, fatou_iterated_unitBall q hq n hn] at hz
  rcases hz with ⟨y, hy, hyz⟩
  have hqz : q (finalLargeVector n) ≤ C := by
    rw [← hyz, q.smul, abs_of_pos hC]
    simpa using mul_le_mul_of_nonneg_left hy hC.le
  have hpz : finalLatticeNorm (finalLargeVector n) = (2 : ℝ) ^ n :=
    (finalLargeVector_properties n).2
  have hlower := (hcompare (finalLargeVector n)).1
  rw [hpz] at hlower
  exact (not_lt_of_ge (hlower.trans hqz)) hlarge
end OrderClosures
