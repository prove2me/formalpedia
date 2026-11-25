-- Prove2me | solution 1 for SNumbers.norm_comp_le_deviationFromRestriction_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:17:12.411729+00:00
-- url     : https://prove2.me/submissions/53694809-aa1d-4a92-8f1d-ab6314d204a0

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
public import Theorems.Thm_SNumbers_deviationFromRestriction_nonneg


set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X] [CompleteSpace Y]
omit [CompleteSpace X] [CompleteSpace Y]
namespace SNumbers
theorem _root_.solution {S : X →L[𝕜] Y}
    {M : Submodule 𝕜 X} {R : X →L[𝕜] X} (hR : ∀ x, R x ∈ M) :
    ‖S.comp R‖ ≤ deviationFromRestriction S M * ‖R‖ := by
  refine opNorm_le_bound _
    (mul_nonneg (deviationFromRestriction_nonneg S M) (norm_nonneg R)) fun x => ?_
  -- Evaluate `S (R x)` through the inclusion `M ↪ X`: it equals
  -- `(S ∘ ι_M) ⟨R x, hR x⟩`, whose norm is `≤ ‖S|_M‖ · ‖R x‖`.
  have h_eq : (S.comp R) x = (S.comp M.subtypeL) ⟨R x, hR x⟩ := rfl
  rw [h_eq]
  calc ‖(S.comp M.subtypeL) ⟨R x, hR x⟩‖
      ≤ ‖S.comp M.subtypeL‖ * ‖(⟨R x, hR x⟩ : M)‖ := (S.comp M.subtypeL).le_opNorm _
    _ = deviationFromRestriction S M * ‖R x‖ := rfl
    _ ≤ deviationFromRestriction S M * (‖R‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (R.le_opNorm x) (deviationFromRestriction_nonneg S M)
    _ = deviationFromRestriction S M * ‖R‖ * ‖x‖ := by ring
end SNumbers
