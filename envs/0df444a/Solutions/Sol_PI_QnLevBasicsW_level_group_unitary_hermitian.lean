-- Prove2me | solution 1 for PI.QnLevBasicsW.level_group_unitary_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:42:32.790065+00:00
-- url     : https://prove2.me/submissions/8350ff04-2030-4eba-afab-a6e246062911

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_eq_c687ca9a93c5
import Theorems.Thm_PI_QnLevBasicsW_Hpk_eq


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
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PI.QnLevBasicsW
theorem _root_.solution : LevUH := by
  intro k i r' g hg
  have hU : gᴴ * Hpk k r' * g = Hpk k r' := hg
  show (ιLev k i r' g)ᴴ * Hpk k (i + r') * ιLev k i r' g = Hpk k (i + r')
  rw [ιLev_eq, Hpk_eq, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hU]
end PI.QnLevBasicsW
