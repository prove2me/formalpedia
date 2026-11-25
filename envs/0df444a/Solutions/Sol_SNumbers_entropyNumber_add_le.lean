-- Prove2me | solution 1 for SNumbers.entropyNumber_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:04.891909+00:00
-- url     : https://prove2.me/submissions/32350aac-4a53-4fa3-912f-f76ea6fb6943

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_entropyNumber_le_norm
public import Theorems.Thm_SNumbers_entropyNumber_additive

set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (S T : X →L[𝕜] Y) (n : ℕ) :
    entropyNumber (S + T) n ≤ entropyNumber S n + ‖T‖ := by
  have h := entropyNumber_additive S T n 0
  rw [Nat.add_zero] at h
  linarith [entropyNumber_le_norm T 0]
end SNumbers
