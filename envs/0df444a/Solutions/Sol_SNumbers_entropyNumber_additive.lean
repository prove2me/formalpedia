-- Prove2me | solution 1 for SNumbers.entropyNumber_additive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:05:01.135687+00:00
-- url     : https://prove2.me/submissions/d90a01b9-e250-41a3-94b8-839023c86c4f

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_entropyNumber_le_of_mem
public import Theorems.Thm_SNumbers_exists_mem_entropySet_lt
public import Theorems.Thm_SNumbers_add_mem_entropySet_add

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
theorem _root_.solution (S T : X →L[𝕜] Y) (n m : ℕ) :
    entropyNumber (S + T) (n + m) ≤ entropyNumber S n + entropyNumber T m := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨ε, hε, hεlt⟩ := exists_mem_entropySet_lt
    (show entropyNumber S n < entropyNumber S n + η / 2 by linarith)
  obtain ⟨δ, hδ, hδlt⟩ := exists_mem_entropySet_lt
    (show entropyNumber T m < entropyNumber T m + η / 2 by linarith)
  calc entropyNumber (S + T) (n + m) ≤ ε + δ :=
        entropyNumber_le_of_mem (add_mem_entropySet_add hε hδ)
    _ ≤ entropyNumber S n + entropyNumber T m + η := by linarith
end SNumbers
