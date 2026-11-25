-- Prove2me | solution 1 for PI.BlockRatReal.antitone_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:06.455058+00:00
-- url     : https://prove2.me/submissions/63bb88db-fbb2-4af9-baa7-17ba58596087

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_AntitoneStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.BlockRatReal
namespace PI.BlockRatReal
theorem _root_.solution {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone fun i : Fin (m + 1) => -lam i.rev :=
  fun _ _ hij => neg_le_neg (h (Fin.rev_le_rev.mpr hij))
end PI.BlockRatReal
