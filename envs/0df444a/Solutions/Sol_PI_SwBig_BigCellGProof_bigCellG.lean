-- Prove2me | solution 1 for PI.SwBig.BigCellGProof.bigCellG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:47.966421+00:00
-- url     : https://prove2.me/submissions/e9dcc275-57f5-453b-8b36-0311600ce7ec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BigCellConjugation_Monomial
import Theorems.Thm_PI_SwBig_BigCellGProof_bigCell_one_apply
import Theorems.Thm_PI_SwBig_BigCellGProof_Hpk_rhoB
import Theorems.Thm_PI_SwBig_BigCellGProof_tv_Hpk_tv
import Theorems.Thm_PI_SwBig_BigCellGProof_conjTranspose_mul_mul_monomial

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
open PI PI.SwBig PI.SwBig.BigCellGProof
open PI.SwBig
namespace PI.SwBig.BigCellGProof
theorem _root_.solution : BigCellG := by
  intro k r c hc
  show (bigCell k r c 1)ᴴ * Hpk k r * bigCell k r c 1 = Hpk k r
  ext i j
  rw [conjTranspose_mul_mul_monomial _ _ (rhoB k r) (tv k r c) (bigCell_one_apply k r c), Hpk_rhoB,
    tv_Hpk_tv k r c hc]
end PI.SwBig.BigCellGProof
