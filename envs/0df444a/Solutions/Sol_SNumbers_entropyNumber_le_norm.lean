-- Prove2me | solution 1 for SNumbers.entropyNumber_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:20:55.274955+00:00
-- url     : https://prove2.me/submissions/fb2bafb2-4aa6-4506-bacc-f3e44a8a6b12

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_norm_add_mem_entropySet
public import Theorems.Thm_SNumbers_entropyNumber_le_of_mem

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
    entropyNumber S n ≤ ‖S‖ :=
  le_of_forall_pos_le_add fun _ hδ =>
    entropyNumber_le_of_mem (norm_add_mem_entropySet S n hδ)
end SNumbers
