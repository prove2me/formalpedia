-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_norm_det_sq_le_fb621fa6f07e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:20.879614+00:00
-- url     : https://prove2.me/submissions/deb31705-fa0a-4ad1-8f43-fab04e186dd7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail
namespace GroundTheory.Heights₂.Heights.LeadBlockGaussTail
theorem _root_.solution {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ) :
    ‖(coordPlaneBlock π).det‖ ^ 2 ≤ (Fintype.card (Equiv.Perm (Fin m)) : ℝ) *
      ∑ σ : Equiv.Perm (Fin m), ∏ i, ‖π i (Fin.castAdd k (σ i))‖ ^ 2 := by
  have h1 : ‖(coordPlaneBlock π).det‖ ≤
      ∑ σ : Equiv.Perm (Fin m), ∏ i, ‖π i (Fin.castAdd k (σ i))‖ := by
    rw [← Matrix.det_transpose, Matrix.det_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
      simp [h, norm_prod, coordPlaneBlock, Matrix.transpose_apply]
  calc ‖(coordPlaneBlock π).det‖ ^ 2
      ≤ (∑ σ : Equiv.Perm (Fin m), ∏ i, ‖π i (Fin.castAdd k (σ i))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Equiv.Perm (Fin m))))
          (f := fun σ => ∏ i, ‖π i (Fin.castAdd k (σ i))‖)
        simpa [Finset.card_univ, Finset.prod_pow] using this
end GroundTheory.Heights₂.Heights.LeadBlockGaussTail
