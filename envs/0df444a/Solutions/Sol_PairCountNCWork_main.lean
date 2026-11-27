-- Prove2me | solution 1 for PairCountNCWork.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:00.510076+00:00
-- url     : https://prove2.me/submissions/0f16c89d-4183-48f0-ab57-0d2297a30f3f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBCardNC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PairCountNoncommuting_OtherFalse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open PairCountNCWork
open Formalism.MainNotions.Ext.CutB
variable {N : ℕ} (ε : Fin N → Bool)
namespace PairCountNCWork
theorem _root_.solution : cBCardNC := by
  intro N ε
  rw [← Fintype.card_congr (equivNC ε), Fintype.card_prod, Fintype.card_subtype,
    Fintype.card_subtype]
  rfl
end PairCountNCWork
