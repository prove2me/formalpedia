-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_conj_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:53:00.769824+00:00
-- url     : https://prove2.me/submissions/c1c24c4b-62de-4ebb-b926-f467894b0cf4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (M k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (K : ℝ)
    (hM : ∀ a b, ‖M a b‖ ≤ K) (i j : Fin n) : ‖(k * M * kᴴ) i j‖ ≤ (n : ℝ) * ((n : ℝ) * K) := by
  have hk' : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hk
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b, ‖(k * M) i b * kᴴ b j‖ ≤ ∑ _b : Fin n, (n : ℝ) * K := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, Matrix.mul_apply]
        have e2 : ‖kᴴ b j‖ ≤ 1 := entry_norm_bound_of_unitary hk' b j
        have e1 : ‖∑ a, k i a * M a b‖ ≤ (n : ℝ) * K := by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ a, ‖k i a * M a b‖ ≤ ∑ _a : Fin n, K := by
                refine Finset.sum_le_sum fun a _ => ?_
                rw [norm_mul]
                calc ‖k i a‖ * ‖M a b‖ ≤ 1 * K :=
                      mul_le_mul (entry_norm_bound_of_unitary hk i a) (hM a b) (norm_nonneg _) zero_le_one
                  _ = K := one_mul K
            _ = (n : ℝ) * K := by simp
        calc ‖∑ a, k i a * M a b‖ * ‖kᴴ b j‖ ≤ ((n : ℝ) * K) * 1 :=
              mul_le_mul e1 e2 (norm_nonneg _) ((norm_nonneg _).trans e1)
          _ = (n : ℝ) * K := mul_one _
    _ = (n : ℝ) * ((n : ℝ) * K) := by simp
end PositivityTheory.Rg.Sw.WR.K.GB
