-- Prove2me | solution 1 for SNumbers.entropyNumber_comp_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:55:20.626939+00:00
-- url     : https://prove2.me/submissions/26e6108d-2ff6-42ba-a053-1a42e275f13b

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_entropyNumber_nonneg
public import Theorems.Thm_SNumbers_entropyNumber_le_norm
public import Theorems.Thm_SNumbers_entropyNumber_multiplicative

set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open SNumbers
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (B : Y →L[𝕜] Z) (S : X →L[𝕜] Y) (A : W →L[𝕜] X)
    (n : ℕ) :
    entropyNumber (B.comp (S.comp A)) n ≤ ‖B‖ * entropyNumber S n * ‖A‖ := by
  have hSA : entropyNumber (S.comp A) n ≤ entropyNumber S n * ‖A‖ := by
    have h := entropyNumber_multiplicative S A n 0
    rw [Nat.add_zero] at h
    exact h.trans
      (mul_le_mul_of_nonneg_left (entropyNumber_le_norm A 0) (entropyNumber_nonneg S n))
  have h := entropyNumber_multiplicative B (S.comp A) 0 n
  rw [Nat.zero_add] at h
  calc entropyNumber (B.comp (S.comp A)) n
      ≤ entropyNumber B 0 * entropyNumber (S.comp A) n := h
    _ ≤ ‖B‖ * (entropyNumber S n * ‖A‖) :=
        mul_le_mul (entropyNumber_le_norm B 0) hSA (entropyNumber_nonneg _ _) (norm_nonneg B)
    _ = ‖B‖ * entropyNumber S n * ‖A‖ := (mul_assoc _ _ _).symm
end SNumbers
