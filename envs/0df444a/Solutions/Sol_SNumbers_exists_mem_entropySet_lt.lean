-- Prove2me | solution 1 for SNumbers.exists_mem_entropySet_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:22:47.886591+00:00
-- url     : https://prove2.me/submissions/37f6b8f4-756e-4b5a-883d-31f0d8c9ac8f

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_entropySet_nonempty

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
theorem _root_.solution {S : X →L[𝕜] Y} {n : ℕ} {b : ℝ}
    (hb : entropyNumber S n < b) :
    ∃ ε ∈ entropySet S n, ε < b :=
  exists_lt_of_csInf_lt (entropySet_nonempty S n) hb
end SNumbers
