-- Prove2me | solution 1 for P2M_PI_MirrorSection__ut_mul_7638fd5817a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:44:47.907087+00:00
-- url     : https://prove2.me/submissions/4b3a6e61-1b12-4e19-8e9a-44f12f4f4dc6

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.MirrorSection₂
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ UTset m) (hb : b ∈ UTset m) : a * b ∈ UTset m := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l < i
    · rw [ha.1 i l hl, zero_mul]
    · rw [hb.1 l j (lt_of_lt_of_le hji (not_lt.mp hl)), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [ha.2, hb.2, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [ha.1 i l h, zero_mul]
      · rw [hb.1 l i h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
end PI.MirrorSection₂
