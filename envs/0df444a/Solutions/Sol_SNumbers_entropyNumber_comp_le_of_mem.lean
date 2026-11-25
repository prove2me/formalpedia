-- Prove2me | solution 1 for SNumbers.entropyNumber_comp_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:32.795096+00:00
-- url     : https://prove2.me/submissions/42354ddc-44b0-4fcf-9a44-16a9913e98c1

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_entropySet_nonempty
public import Theorems.Thm_SNumbers_entropyNumber_le_of_mem
public import Theorems.Thm_SNumbers_mul_mem_entropySet_comp

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
theorem _root_.solution {B : Y →L[𝕜] Z} {S : X →L[𝕜] Y} {n m : ℕ} {δ : ℝ}
    (hδ : δ ∈ entropySet S m) {c : 𝕜} (hc : δ < ‖c‖) :
    entropyNumber (B.comp S) (n + m) ≤ ‖c‖ * entropyNumber B n := by
  have hc0 : (0 : ℝ) < ‖c‖ := hδ.1.trans hc
  rw [← div_le_iff₀' hc0]
  refine le_csInf (entropySet_nonempty B n) fun β hβ => ?_
  rw [div_le_iff₀' hc0]
  exact entropyNumber_le_of_mem (mul_mem_entropySet_comp hβ hδ hc)
end SNumbers
