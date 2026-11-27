-- Prove2me | solution 1 for big_cell_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:34:30.403705+00:00
-- url     : https://prove2.me/submissions/33302775-1270-427f-9b1e-a771c36ba3d1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BigCellConjugation_Monomial
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SwBigCellG
import Theorems.Thm_PI_SwBig_BigCellGProof_bigCellG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.SwBig.BigCellG := PI.SwBig.BigCellGProof.bigCellG
