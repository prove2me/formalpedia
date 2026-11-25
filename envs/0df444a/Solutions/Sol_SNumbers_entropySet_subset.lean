-- Prove2me | solution 1 for SNumbers.entropySet_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:53.664925+00:00
-- url     : https://prove2.me/submissions/9a50c112-ab7f-4f01-b9d4-ae41a02240e7

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
theorem _root_.solution (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    entropySet S n ⊆ entropySet S m := by
  rintro ε ⟨hε, N, hN, hcov⟩
  exact ⟨hε, N, hN.trans (Nat.pow_le_pow_right (by norm_num) h), hcov⟩
end SNumbers
