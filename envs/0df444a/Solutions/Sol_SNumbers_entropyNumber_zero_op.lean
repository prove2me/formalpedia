-- Prove2me | solution 1 for SNumbers.entropyNumber_zero_op
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:49.288491+00:00
-- url     : https://prove2.me/submissions/74c351b0-ff8b-4743-a2b7-90b612a15e12

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_entropyNumber_def
public import Theorems.Thm_SNumbers_entropySet_zero_op

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
theorem _root_.solution (n : ℕ) :
    entropyNumber (0 : X →L[𝕜] Y) n = 0 := by
  rw [entropyNumber_def, entropySet_zero_op, csInf_Ioi]
end SNumbers
