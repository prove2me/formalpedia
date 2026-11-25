-- Prove2me | solution 1 for PositivityTheory.CW.AdjointWordFiltration.adjSign_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:25:20.766603+00:00
-- url     : https://prove2.me/submissions/6f275e4f-9ed2-4b7e-9fe1-d1a998a73036

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CasimirPowerCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.AdjointWordFiltration
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.AdjointWordFiltration
theorem _root_.solution (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b * adjSign ε a b = 1 := by
  unfold adjSign; split_ifs <;> norm_num
end PositivityTheory.CW.AdjointWordFiltration
