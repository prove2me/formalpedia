-- Prove2me | solution 1 for SNumbers.Lifting.norm_le_norm_comp_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:49:04.007978+00:00
-- url     : https://prove2.me/submissions/6f5f9612-7234-4489-910d-f3b00e48feee

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_KolmogorovLifting
public import Theorems.Thm_SNumbers_Lifting_Q_single
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] Submodule.liftQL_mkQL


section
@[expose] public section
universe u
open scoped Cardinal NNReal ENNReal
open ContinuousLinearMap
namespace SNumbers
namespace Lifting
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X]
section S1a
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
private lemma exists_lift_of_pos_norm
    {x : X} (hx : 0 < ‖x‖) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (c : 𝕜) (h_in : ‖c⁻¹ • x‖ ≤ 1),
      ‖x‖ < ‖c‖ ∧ ‖c‖ < ‖x‖ + δ ∧
      (Q : BallLp 𝕜 X →L[𝕜] X)
          (letI := Classical.decEq (Ball X);
           lp.single 1 (⟨c⁻¹ • x, h_in⟩ : Ball X) c) = x ∧
      (letI := Classical.decEq (Ball X);
       ‖lp.single (E := fun _ : Ball X => 𝕜) 1 (⟨c⁻¹ • x, h_in⟩ : Ball X) c‖) = ‖c‖ := by
  obtain ⟨c, hc_lb, hc_ub⟩ :=
    NormedField.exists_lt_norm_lt 𝕜 hx.le (lt_add_of_pos_right _ hδ)
  have hc_pos : 0 < ‖c‖ := hx.trans hc_lb
  have hc_ne : c ≠ 0 := norm_pos_iff.mp hc_pos
  have h_in : ‖c⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, norm_inv, inv_mul_le_iff₀ hc_pos, mul_one]; exact hc_lb.le
  refine ⟨c, h_in, hc_lb, hc_ub, ?_, ?_⟩
  · rw [Q_single _ h_in c, smul_smul, mul_inv_cancel₀ hc_ne, one_smul]
  · let := Classical.decEq (Ball X)
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
end S1a
section S3
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
end S3
section S5
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {X : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
end S5
section S5b
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
end S5b
section Pietsch
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
end Pietsch
end Lifting
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal NNReal ENNReal
open ContinuousLinearMap
open SNumbers
open SNumbers.Lifting
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X]
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers.Lifting
theorem _root_.solution {Z : Type u} [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (B : X →L[𝕜] Z) : ‖B‖ ≤ ‖B.comp (Q : BallLp 𝕜 X →L[𝕜] X)‖ := by
  set M := ‖B.comp (Q : BallLp 𝕜 X →L[𝕜] X)‖ with hM
  have hM_nn : 0 ≤ M := norm_nonneg _
  refine opNorm_le_bound _ hM_nn fun x => ?_
  by_cases hx : x = 0
  · simp [hx]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hM1_pos : (0 : ℝ) < M + 1 := by linarith
  obtain ⟨c, h_in, _hc_lb, hc_ub, hQα, hαnorm⟩ :=
    exists_lift_of_pos_norm (𝕜 := 𝕜) (X := X) (norm_pos_iff.mpr hx)
      (div_pos hε hM1_pos)
  let : DecidableEq (Ball X) := Classical.decEq _
  have h_op := (B.comp (Q : BallLp 𝕜 X →L[𝕜] X)).le_opNorm
                (lp.single 1 (⟨c⁻¹ • x, h_in⟩ : Ball X) c)
  rw [coe_comp, Function.comp_apply, hQα, hαnorm] at h_op
  -- `h_op : ‖B x‖ ≤ M * ‖c‖`; then `M * ‖c‖ ≤ M * ‖x‖ + ε` via `‖c‖ < ‖x‖ + δ`.
  have hMc : M * ‖c‖ ≤ M * ‖x‖ + ε := by
    calc M * ‖c‖
        ≤ M * (‖x‖ + ε / (M + 1)) := mul_le_mul_of_nonneg_left hc_ub.le hM_nn
      _ = M * ‖x‖ + (M / (M + 1)) * ε := by ring
      _ ≤ M * ‖x‖ + 1 * ε := by
          gcongr; exact (div_le_one hM1_pos).mpr (by linarith)
      _ = M * ‖x‖ + ε := by ring
  linarith
end SNumbers.Lifting
