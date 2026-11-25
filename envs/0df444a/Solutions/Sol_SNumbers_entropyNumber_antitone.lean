-- Prove2me | solution 1 for SNumbers.entropyNumber_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:05:32.996367+00:00
-- url     : https://prove2.me/submissions/d331137a-97aa-4ab4-a550-a54aa2262e5b

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_P2M_SNumbers_entropyNumber_antitone__7948be0d85af

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
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    entropyNumber S (n + 1) ≤ entropyNumber S n :=
  entropyNumber_antitone' S (Nat.le_succ n)
end SNumbers
