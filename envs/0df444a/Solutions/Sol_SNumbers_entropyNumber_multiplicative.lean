-- Prove2me | solution 1 for SNumbers.entropyNumber_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:49:01.997628+00:00
-- url     : https://prove2.me/submissions/4f116833-2274-4c33-a817-2dff7129d173

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_exists_mem_entropySet_lt
public import Theorems.Thm_SNumbers_entropyNumber_nonneg
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_entropyNumber_comp_le_of_mem
attribute [local simp] SNumbers.entropyNumber_zero_op

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
theorem _root_.solution (B : Y →L[𝕜] Z) (S : X →L[𝕜] Y) (n m : ℕ) :
    entropyNumber (B.comp S) (n + m) ≤ entropyNumber B n * entropyNumber S m := by
  -- first: the bound with an arbitrary slack `t > 0` on the factor for `S`
  have key : ∀ t : ℝ, 0 < t →
      entropyNumber (B.comp S) (n + m) ≤ entropyNumber B n * (entropyNumber S m + t) := by
    intro t ht
    obtain ⟨δ, hδ, hδlt⟩ := exists_mem_entropySet_lt
      (show entropyNumber S m < entropyNumber S m + t / 2 by linarith)
    obtain ⟨c, hc1, hc2⟩ :=
      NormedField.exists_lt_norm_lt 𝕜 hδ.1.le (show δ < δ + t / 2 by linarith)
    calc entropyNumber (B.comp S) (n + m) ≤ ‖c‖ * entropyNumber B n :=
          entropyNumber_comp_le_of_mem hδ hc1
      _ ≤ (entropyNumber S m + t) * entropyNumber B n := by
          gcongr
          · exact entropyNumber_nonneg B n
          · linarith
      _ = entropyNumber B n * (entropyNumber S m + t) := mul_comm _ _
  -- then: let the slack tend to `0`
  refine le_of_forall_pos_le_add fun κ hκ => ?_
  rcases eq_or_lt_of_le (entropyNumber_nonneg B n) with hB | hB
  · have h0 := key 1 one_pos
    rw [← hB] at h0 ⊢
    simp only [zero_mul] at h0 ⊢
    linarith
  · have h := key (κ / entropyNumber B n) (by positivity)
    rwa [mul_add, mul_div_cancel₀ _ hB.ne'] at h
end SNumbers
