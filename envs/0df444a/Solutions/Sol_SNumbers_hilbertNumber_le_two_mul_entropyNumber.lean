-- Prove2me | solution 1 for SNumbers.hilbertNumber_le_two_mul_entropyNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:24:25.760007+00:00
-- url     : https://prove2.me/submissions/41cafaed-49cc-4aa9-ba2d-7a23e0c653d3

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_SNumbers_approximationNumber_le_two_mul_entropyNumber
public import Theorems.Thm_SNumbers_entropyNumber_comp_comp_le
public import Theorems.Thm_SNumbers_entropyNumber_nonneg
public import Theorems.Thm_SNumbers_hilbertNumber_def


set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S n ≤ 2 * entropyNumber S n := by
  rw [hilbertNumber_def]
  refine Real.sSup_le ?_ (by positivity [entropyNumber_nonneg S n])
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
  rw [div_le_iff₀ hpos]
  calc approximationNumber (B.comp (S.comp A)) n
      ≤ 2 * entropyNumber (B.comp (S.comp A)) n :=
        approximationNumber_le_two_mul_entropyNumber _ n
    _ ≤ 2 * (‖B‖ * entropyNumber S n * ‖A‖) := by
        have := entropyNumber_comp_comp_le B S A n
        linarith
    _ = 2 * entropyNumber S n * (‖B‖ * ‖A‖) := by ring
end SNumbers
