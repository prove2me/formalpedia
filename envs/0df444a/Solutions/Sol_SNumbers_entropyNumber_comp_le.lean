-- Prove2me | solution 1 for SNumbers.entropyNumber_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:24:15.446382+00:00
-- url     : https://prove2.me/submissions/60c0302c-13a3-452b-b430-e7ffc5d91502

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_entropySet_nonempty
public import Theorems.Thm_SNumbers_entropyNumber_le_of_mem
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_norm_mul_mem_entropySet_comp
attribute [local simp] SNumbers.entropyNumber_zero_op

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
theorem _root_.solution (B : Y →L[𝕜] Z) (S : X →L[𝕜] Y) (n : ℕ) :
    entropyNumber (B.comp S) n ≤ ‖B‖ * entropyNumber S n := by
  rcases eq_or_lt_of_le (norm_nonneg B) with hB | hB
  · have hB0 : B = 0 := by rwa [eq_comm, norm_eq_zero] at hB
    simp [hB0]
  · rw [← div_le_iff₀' hB]
    refine le_csInf (entropySet_nonempty S n) fun ε hε => ?_
    rw [div_le_iff₀' hB]
    exact entropyNumber_le_of_mem (norm_mul_mem_entropySet_comp hB hε)
end SNumbers
