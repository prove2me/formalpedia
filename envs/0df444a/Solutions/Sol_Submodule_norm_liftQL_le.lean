-- Prove2me | solution 1 for Submodule.norm_liftQL_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:13:08.188851+00:00
-- url     : https://prove2.me/submissions/704e691a-1fc5-426c-bc33-33e3131b17b6

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Group.Quotient
public import Definitions.Def_SNumbers_QuotientMapNorms

set_option autoImplicit true
@[expose] public section
public section
open Submodule
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {Y Z : Type*}
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace Submodule
theorem _root_.solution (V : Submodule 𝕜 Y) (f : Y →L[𝕜] Z)
    (h : V ≤ LinearMap.ker (f : Y →ₗ[𝕜] Z)) :
    ‖V.liftQL f h‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
    -- For each `x : Y ⧸ V`, take a representative `y` with `‖y‖ ≤ ‖x‖ + ε`.
    -- Then `liftQL f h x = f y`, so `‖liftQL f h x‖ ≤ ‖f‖ * ‖y‖ ≤ ‖f‖ * (‖x‖ + ε)`,
    -- and `ε → 0`.
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hf_pos : (0 : ℝ) < ‖f‖ + 1 := by positivity
    obtain ⟨y, hy_eq, hy_norm⟩ :=
      Submodule.Quotient.norm_mk_lt x (div_pos hε hf_pos)
    have h_eq : V.liftQL f h x = f y := by
      rw [V.liftQL_apply, ← hy_eq]
      exact V.liftQ_apply (f : Y →ₗ[𝕜] Z) y
    rw [h_eq]
    calc ‖f y‖
        ≤ ‖f‖ * ‖y‖ := f.le_opNorm y
      _ ≤ ‖f‖ * (‖x‖ + ε / (‖f‖ + 1)) :=
          mul_le_mul_of_nonneg_left hy_norm.le (norm_nonneg _)
      _ = ‖f‖ * ‖x‖ + ‖f‖ / (‖f‖ + 1) * ε := by ring
      _ ≤ ‖f‖ * ‖x‖ + 1 * ε := by
          gcongr
          rw [div_le_one hf_pos]; linarith [norm_nonneg f]
      _ = ‖f‖ * ‖x‖ + ε := by ring
end Submodule
