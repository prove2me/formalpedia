-- Prove2me | solution 1 for SNumbers.kolmogorovNumber_comp_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:47.137684+00:00
-- url     : https://prove2.me/submissions/2924b1f8-628a-4102-9f55-7246718f3341

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_SNumbers_kolmogorovNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_kolmogorovNumber_multiplicative

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
    kolmogorovNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * kolmogorovNumber S n * ‖A‖ := by
  have hSA : kolmogorovNumber (S.comp A) n ≤ kolmogorovNumber S n * ‖A‖ := by
    have h := kolmogorovNumber_multiplicative S A n 0
    rwa [Nat.add_zero, kolmogorovNumber_zero_eq_norm] at h
  have hB : kolmogorovNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * kolmogorovNumber (S.comp A) n := by
    have h := kolmogorovNumber_multiplicative B (S.comp A) 0 n
    rwa [Nat.zero_add, kolmogorovNumber_zero_eq_norm] at h
  calc kolmogorovNumber (B.comp (S.comp A)) n
      ≤ ‖B‖ * kolmogorovNumber (S.comp A) n := hB
    _ ≤ ‖B‖ * (kolmogorovNumber S n * ‖A‖) :=
        mul_le_mul_of_nonneg_left hSA (norm_nonneg B)
    _ = ‖B‖ * kolmogorovNumber S n * ‖A‖ := (mul_assoc _ _ _).symm
end SNumbers
