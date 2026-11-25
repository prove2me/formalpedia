-- Prove2me | solution 1 for SNumbers.approximationNumber_comp_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:52.553018+00:00
-- url     : https://prove2.me/submissions/6b8200e4-bd9d-4201-99fa-be3c831cce65

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_approximationNumber_multiplicative
public import Theorems.Thm_ContinuousLinearMap_rank_zero
attribute [local simp] ContinuousLinearMap.rank_zero


attribute [local simp] SNumbers.approximationNumber_zero_eq_norm

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
    approximationNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * approximationNumber S n * ‖A‖ := by
  have hSA : approximationNumber (S.comp A) n ≤ approximationNumber S n * ‖A‖ := by
    have h := approximationNumber_multiplicative S A n 0
    rwa [Nat.add_zero, approximationNumber_zero_eq_norm] at h
  have hB : approximationNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * approximationNumber (S.comp A) n := by
    have h := approximationNumber_multiplicative B (S.comp A) 0 n
    rwa [Nat.zero_add, approximationNumber_zero_eq_norm] at h
  calc approximationNumber (B.comp (S.comp A)) n
      ≤ ‖B‖ * approximationNumber (S.comp A) n := hB
    _ ≤ ‖B‖ * (approximationNumber S n * ‖A‖) :=
        mul_le_mul_of_nonneg_left hSA (norm_nonneg B)
    _ = ‖B‖ * approximationNumber S n * ‖A‖ := (mul_assoc _ _ _).symm
end SNumbers
