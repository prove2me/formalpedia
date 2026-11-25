-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.inst_rank_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:27.752598+00:00
-- url     : https://prove2.me/submissions/d45f9448-64e9-4b5f-b527-3279daa3ec4f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstAdapt

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
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) : (X + Y).rank ≤ X.rank + Y.rank := by
  first
    | exact Matrix.rank_add_le X Y
    | (unfold Matrix.rank
       rw [Matrix.mulVecLin_add]
       exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
         (Submodule.finrank_add_le_finrank_add_finrank _ _))
end PI.ScMuExists.UnitaryGroupMassFormula
