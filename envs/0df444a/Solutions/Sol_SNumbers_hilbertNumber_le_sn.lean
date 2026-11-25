-- Prove2me | solution 1 for SNumbers.hilbertNumber_le_sn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:22:41.445709+00:00
-- url     : https://prove2.me/submissions/5243f370-71be-4f80-8735-379cc12ba7d7

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
public import Theorems.Thm_SNumbers_approximationNumber_le_sn
public import Theorems.Thm_SNumbers_hilbertNumber_def


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
namespace SNumbers
theorem _root_.solution {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S n ≤ s S n := by
  rw [hilbertNumber_def]
  refine Real.sSup_le ?_ (hs.nonneg S n)
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
  rw [div_le_iff₀ hpos]
  -- `B ∘ S ∘ A : ℓ₂ → ℓ₂` is between Hilbert spaces, so `aₙ = sₙ` on it.
  calc approximationNumber (B.comp (S.comp A)) n
      ≤ s (B.comp (S.comp A)) n := approximationNumber_le_sn hs (B.comp (S.comp A)) n
    _ ≤ ‖B‖ * s S n * ‖A‖ := hs.ideal A S B n
    _ = s S n * (‖B‖ * ‖A‖) := by ring
end SNumbers
