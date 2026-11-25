-- Prove2me | solution 1 for SNumbers.hilbertNumber_additive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:08:22.788284+00:00
-- url     : https://prove2.me/submissions/af0fe105-7b40-4471-a38c-c6ee5fa84a4f

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
public import Theorems.Thm_SNumbers_hilbertNumber_def
public import Theorems.Thm_SNumbers_ratio_le_hilbertNumber
public import Theorems.Thm_SNumbers_hilbertNumber_nonneg
public import Theorems.Thm_SNumbers_approximationNumber_additive


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (S T : X →L[𝕜] Y) (n m : ℕ) :
    hilbertNumber (S + T) (n + m) ≤ hilbertNumber S n + hilbertNumber T m := by
  rw [hilbertNumber_def]
  refine Real.sSup_le ?_ (add_nonneg (hilbertNumber_nonneg S n) (hilbertNumber_nonneg T m))
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
  -- `B ∘ (S + T) ∘ A = B∘S∘A + B∘T∘A`.
  have hcomp : B.comp ((S + T).comp A) = B.comp (S.comp A) + B.comp (T.comp A) := by
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  have hS := ratio_le_hilbertNumber S n hA hB
  have hT := ratio_le_hilbertNumber T m hA hB
  rw [div_le_iff₀ hpos] at hS hT
  rw [hcomp, div_le_iff₀ hpos]
  calc approximationNumber (B.comp (S.comp A) + B.comp (T.comp A)) (n + m)
      ≤ approximationNumber (B.comp (S.comp A)) n +
          approximationNumber (B.comp (T.comp A)) m :=
        approximationNumber_additive _ _ n m
    _ ≤ hilbertNumber S n * (‖B‖ * ‖A‖) + hilbertNumber T m * (‖B‖ * ‖A‖) :=
        add_le_add hS hT
    _ = (hilbertNumber S n + hilbertNumber T m) * (‖B‖ * ‖A‖) := by ring
end SNumbers
