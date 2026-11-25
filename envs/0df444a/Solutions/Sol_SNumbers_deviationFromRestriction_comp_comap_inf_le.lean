-- Prove2me | solution 1 for SNumbers.deviationFromRestriction_comp_comap_inf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:27:55.747612+00:00
-- url     : https://prove2.me/submissions/49eb9a16-bf84-4a61-ac99-523e2fc47db0

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_deviationFromRestriction_nonneg
public import Theorems.Thm_SNumbers_norm_apply_le_deviationFromRestriction_mul

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
theorem _root_.solution (S : Y →L[𝕜] Z) (T : X →L[𝕜] Y)
    (M : Submodule 𝕜 Y) (N : Submodule 𝕜 X) :
    deviationFromRestriction (S.comp T) (M.comap (T : X →ₗ[𝕜] Y) ⊓ N) ≤
      deviationFromRestriction S M * deviationFromRestriction T N := by
  refine opNorm_le_bound ((S.comp T).comp (M.comap (T : X →ₗ[𝕜] Y) ⊓ N).subtypeL)
    (mul_nonneg (deviationFromRestriction_nonneg S M) (deviationFromRestriction_nonneg T N))
    fun x => ?_
  -- `x` lies in `N`, and `T x` lies in `M`
  have hTx : T (x : X) ∈ M := Submodule.mem_comap.mp (Submodule.mem_inf.mp x.2).1
  have hxN : (x : X) ∈ N := (Submodule.mem_inf.mp x.2).2
  calc ‖((S.comp T).comp (M.comap (T : X →ₗ[𝕜] Y) ⊓ N).subtypeL) x‖
      = ‖S (T (x : X))‖ := rfl
    _ ≤ deviationFromRestriction S M * ‖T (x : X)‖ :=
        norm_apply_le_deviationFromRestriction_mul S hTx
    _ ≤ deviationFromRestriction S M * (deviationFromRestriction T N * ‖(x : X)‖) :=
        mul_le_mul_of_nonneg_left (norm_apply_le_deviationFromRestriction_mul T hxN)
          (deviationFromRestriction_nonneg S M)
    _ = deviationFromRestriction S M * deviationFromRestriction T N * ‖x‖ :=
        (mul_assoc _ _ _).symm
end SNumbers
