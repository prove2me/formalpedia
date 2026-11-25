-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.norm_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:44.091173+00:00
-- url     : https://prove2.me/submissions/02c80e3a-f3c1-48a5-9731-a0856c584f0b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_sq_ge

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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {M : Matrix (Fin n) (Fin n) ℂ} (y : E n) (hM : Mᴴ * M = 1 + herm y * herm y)
    (hd : M.det ≠ 0) (a b : Fin n) : ‖M⁻¹ a b‖ ≤ 1 := by
  have hMx : M *ᵥ (M⁻¹ *ᵥ Pi.single b 1) = Pi.single b 1 := by
    rw [mulVec_mulVec, mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hd), one_mulVec]
  have h1 := norm_sq_ge y hM (M⁻¹ *ᵥ Pi.single b 1)
  rw [hMx] at h1
  have hsum1 : ∑ i, ‖(Pi.single b (1 : ℂ) : Fin n → ℂ) i‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  have hxa : (M⁻¹ *ᵥ Pi.single b 1) a = M⁻¹ a b := by
    simp [mulVec, dotProduct, Pi.single_apply]
  have h2 : ‖M⁻¹ a b‖ ^ 2 ≤ 1 := by
    rw [← hxa, ← hsum1]
    refine le_trans ?_ h1
    exact Finset.single_le_sum (f := fun i => ‖(M⁻¹ *ᵥ Pi.single b 1) i‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ a)
  nlinarith [norm_nonneg (M⁻¹ a b)]
end PositivityTheory.Rg.Sw.WR.B
