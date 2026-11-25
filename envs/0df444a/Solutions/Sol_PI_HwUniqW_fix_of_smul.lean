-- Prove2me | solution 1 for PI.HwUniqW.fix_of_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:43:10.626021+00:00
-- url     : https://prove2.me/submissions/22d547a7-5260-486d-9acf-7ca171bde365

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector

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
open PI PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}
namespace PI.HwUniqW
theorem _root_.solution {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {s : ℂ} (hs : s ≠ 0)
    {w : Fin (2 * r + k + 1) → ℂ} (h : m *ᵥ (s • w) = s • w) : m *ᵥ w = w := by
  rw [Matrix.mulVec_smul] at h
  exact smul_right_injective _ hs h
end PI.HwUniqW
