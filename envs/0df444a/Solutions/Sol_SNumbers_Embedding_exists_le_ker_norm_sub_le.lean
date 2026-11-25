-- Prove2me | solution 1 for SNumbers.Embedding.exists_le_ker_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:15:03.05081+00:00
-- url     : https://prove2.me/submissions/e8bb4c0a-b386-47da-bb90-2e7dd96c7539

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_GelfandEmbedding
public import Theorems.Thm_SNumbers_Embedding_toLInfty_apply
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_IsMetricInjection_norm_le_one
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] Submodule.liftQL_mkQL


attribute [local simp] SNumbers.Embedding.toLInfty_apply

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
open SNumbers.Embedding
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers.Embedding
theorem _root_.solution (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    ∃ L : X →L[𝕜] lp (fun _ : DualBall 𝕜 Y => 𝕜) ∞,
      M ≤ LinearMap.ker (L : X →ₗ[𝕜] lp (fun _ : DualBall 𝕜 Y => 𝕜) ∞) ∧
        ‖(J : Y →L[𝕜] _).comp S - L‖ ≤ ‖S.comp M.subtypeL‖ := by
  set d := ‖S.comp M.subtypeL‖ with hd
  -- The restricted functionals `(φ ∘ S)|_M` have norm at most `d`.
  have hψ : ∀ φ : DualBall 𝕜 Y, ‖((φ : Y →L[𝕜] 𝕜).comp S).comp M.subtypeL‖ ≤ d := by
    intro φ
    calc ‖((φ : Y →L[𝕜] 𝕜).comp S).comp M.subtypeL‖
        = ‖(φ : Y →L[𝕜] 𝕜).comp (S.comp M.subtypeL)‖ := rfl
      _ ≤ ‖(φ : Y →L[𝕜] 𝕜)‖ * d := opNorm_comp_le _ _
      _ ≤ 1 * d := mul_le_mul_of_nonneg_right (norm_le_one φ) (norm_nonneg _)
      _ = d := one_mul _
  -- Hahn–Banach extensions `g φ` of the restricted functionals, of the same norm.
  choose g hg_ext hg_norm using fun φ : DualBall 𝕜 Y =>
    exists_extension_norm_eq M (((φ : Y →L[𝕜] 𝕜).comp S).comp M.subtypeL)
  have hg_le : ∀ φ, ‖g φ‖ ≤ d := fun φ => (hg_norm φ).trans_le (hψ φ)
  have hd0 : 0 ≤ d := norm_nonneg _
  -- The approximant `L x = (φ(S x) - g φ x)_φ`.
  have hL : ∀ φ : DualBall 𝕜 Y, ‖(φ : Y →L[𝕜] 𝕜).comp S - g φ‖ ≤ ‖S‖ + d := fun φ =>
    (norm_sub_le _ _).trans (add_le_add
      ((opNorm_comp_le _ _).trans
        ((mul_le_mul_of_nonneg_right (norm_le_one φ) (norm_nonneg _)).trans_eq (one_mul _)))
      (hg_le φ))
  set L := toLInfty (fun φ : DualBall 𝕜 Y => (φ : Y →L[𝕜] 𝕜).comp S - g φ) (by positivity) hL
    with hL_def
  refine ⟨L, ?_, ?_⟩
  · -- `L` vanishes on `M`: `g φ` agrees with `φ ∘ S` there.
    intro m hm
    rw [LinearMap.mem_ker]
    ext φ
    have h := hg_ext φ ⟨m, hm⟩
    simp only [coe_comp, Function.comp_apply, Submodule.coe_subtypeL,
      Submodule.coe_subtype] at h
    simp [hL_def, h]
  · -- `(J_Y S - L) x = (g φ x)_φ`.
    refine opNorm_le_bound _ hd0 fun x => ?_
    refine lp.norm_le_of_forall_le (mul_nonneg hd0 (norm_nonneg x)) fun φ => ?_
    have hcoord : (((J : Y →L[𝕜] _).comp S - L) x : DualBall 𝕜 Y → 𝕜) φ = g φ x := by
      simp [hL_def, J]
    rw [hcoord]
    exact (g φ).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hg_le φ) (norm_nonneg x))
end SNumbers.Embedding
