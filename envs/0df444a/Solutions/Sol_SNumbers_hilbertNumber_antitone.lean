-- Prove2me | solution 1 for SNumbers.hilbertNumber_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:40.954088+00:00
-- url     : https://prove2.me/submissions/465d206e-9e72-4745-87b1-06c2a6bf5d75

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
public import Theorems.Thm_SNumbers_hilbertNumber_def
public import Theorems.Thm_SNumbers_ratio_le_hilbertNumber
public import Theorems.Thm_SNumbers_hilbertNumber_nonneg
public import Theorems.Thm_SNumbers_approximationNumber_antitone


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
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S (n + 1) ≤ hilbertNumber S n := by
  rw [hilbertNumber_def]
  refine Real.sSup_le ?_ (hilbertNumber_nonneg S n)
  rintro r ⟨A, B, hA, hB, rfl⟩
  refine le_trans ?_ (ratio_le_hilbertNumber S n hA hB)
  gcongr
  exact approximationNumber_antitone _ _
end SNumbers
