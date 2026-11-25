-- Prove2me | solution 1 for PI.FrameInd.finrank_Uperp_of_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:56:23.182905+00:00
-- url     : https://prove2.me/submissions/ad677765-6c8e-443d-aeb1-fd4920be0512

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_FinrankUperpOfDet
import Theorems.Thm_PI_FrameInd_gramM_eq
import Theorems.Thm_PI_FrameInd_Uperp_mat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.FrameInd
namespace PI.FrameInd
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hdet : (gramM k r z z' g).det ≠ 0) :
    Module.finrank ℂ (Uperp k r z z' g) = k - 1 := by
  obtain ⟨R, hR⟩ : ∃ R, R = (Vc k r z z' g)ᴴ * Hpk k r := ⟨_, rfl⟩
  have hRV : R * Vc k r z z' g = gramM k r z z' g := by rw [hR, gramM_eq]
  have hrk1 : (gramM k r z z' g).rank = 2 * r + 2 := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))]
    simp; ring
  have hrk2 : (gramM k r z z' g).rank ≤ R.rank := by rw [← hRV]; exact Matrix.rank_mul_le_left _ _
  have hrk3 : R.rank ≤ 2 * r + 2 := by
    have := Matrix.rank_le_card_height R
    simp at this; omega
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin R)
  have hrank : R.rank = Module.finrank ℂ (LinearMap.range (Matrix.mulVecLin R)) := rfl
  rw [Uperp_mat, ← hR]
  simp only [Module.finrank_fin_fun] at hrn
  omega
end PI.FrameInd
