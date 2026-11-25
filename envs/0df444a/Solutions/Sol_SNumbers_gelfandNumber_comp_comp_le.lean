-- Prove2me | solution 1 for SNumbers.gelfandNumber_comp_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:00:23.426382+00:00
-- url     : https://prove2.me/submissions/a32e871b-fc5a-49e2-95d9-f9e5429201e5

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_gelfandNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_gelfandNumber_multiplicative

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
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    gelfandNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * gelfandNumber S n * ‖A‖ := by
  have hSA : gelfandNumber (S.comp A) n ≤ gelfandNumber S n * ‖A‖ := by
    have h := gelfandNumber_multiplicative S A n 0
    rwa [Nat.add_zero, gelfandNumber_zero_eq_norm] at h
  have hB : gelfandNumber (B.comp (S.comp A)) n ≤ ‖B‖ * gelfandNumber (S.comp A) n := by
    have h := gelfandNumber_multiplicative B (S.comp A) 0 n
    rwa [Nat.zero_add, gelfandNumber_zero_eq_norm] at h
  calc gelfandNumber (B.comp (S.comp A)) n
      ≤ ‖B‖ * gelfandNumber (S.comp A) n := hB
    _ ≤ ‖B‖ * (gelfandNumber S n * ‖A‖) := mul_le_mul_of_nonneg_left hSA (norm_nonneg B)
    _ = ‖B‖ * gelfandNumber S n * ‖A‖ := (mul_assoc _ _ _).symm
end SNumbers
