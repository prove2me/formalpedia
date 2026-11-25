-- Prove2me | solution 1 for SNumbers.deviationFromRestriction_comp_comp_comap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:19:25.512872+00:00
-- url     : https://prove2.me/submissions/1daa82f7-6755-4657-8854-f8d0ab1692a0

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (M : Submodule 𝕜 X) :
    deviationFromRestriction (B.comp (S.comp A))
        (M.comap (A : W →ₗ[𝕜] X))
      ≤ ‖B‖ * ‖A‖ * deviationFromRestriction S M := by
  unfold deviationFromRestriction
  -- Pointwise on `M' := M.comap A`. For `w ∈ M'` we have `A w ∈ M`, so we can
  -- evaluate `S ∘ ι_M` at `⟨A w, w.2⟩` and chain `le_opNorm` for `B`, for
  -- `S ∘ ι_M`, and for `A`.
  have h_bound_nn : 0 ≤ ‖B‖ * ‖A‖ * ‖S.comp M.subtypeL‖ :=
    mul_nonneg (mul_nonneg (norm_nonneg B) (norm_nonneg A))
      (norm_nonneg (S.comp M.subtypeL))
  refine opNorm_le_bound _ h_bound_nn fun w => ?_
  set y : M := ⟨A (w : W), w.2⟩
  show ‖B (S (A (w : W)))‖ ≤ ‖B‖ * ‖A‖ * ‖S.comp M.subtypeL‖ * ‖w‖
  have h_y : S (A (w : W)) = (S.comp M.subtypeL) y := rfl
  rw [h_y]
  calc ‖B ((S.comp M.subtypeL) y)‖
      ≤ ‖B‖ * ‖(S.comp M.subtypeL) y‖ := B.le_opNorm _
    _ ≤ ‖B‖ * (‖S.comp M.subtypeL‖ * ‖A (w : W)‖) := by
        gcongr; exact (S.comp M.subtypeL).le_opNorm y
    _ ≤ ‖B‖ * (‖S.comp M.subtypeL‖ * (‖A‖ * ‖w‖)) := by
        gcongr; exact A.le_opNorm (w : W)
    _ = ‖B‖ * ‖A‖ * ‖S.comp M.subtypeL‖ * ‖w‖ := by ring
end SNumbers
