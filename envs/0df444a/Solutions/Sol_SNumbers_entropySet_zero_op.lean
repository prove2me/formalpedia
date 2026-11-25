-- Prove2me | solution 1 for SNumbers.entropySet_zero_op
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:56.435806+00:00
-- url     : https://prove2.me/submissions/5ec287ad-e857-40e9-a530-9326da773b66

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy

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
    entropySet (0 : X →L[𝕜] Y) n = Set.Ioi 0 := by
  ext ε
  refine ⟨fun h => h.1, fun hε => ⟨hε, {0}, by simpa using Nat.one_le_two_pow, ?_⟩⟩
  rintro _ ⟨x, -, rfl⟩
  simpa using le_of_lt hε
end SNumbers
