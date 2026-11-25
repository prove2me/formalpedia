-- Prove2me | solution 1 for PI.SqfDivDeg.W.sum_rts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:24:03.984157+00:00
-- url     : https://prove2.me/submissions/e5b35cc6-4053-4410-99ed-7cc4c7510368

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_CardMonicTwoRootsLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
open Classical
namespace PI.SqfDivDeg.W
theorem _root_.solution {g : ℕ} [Fact g.Prime] (S : Finset (ZMod g)[X]) :
    ∑ f ∈ S, (rts f).card = ∑ c : ZMod g, (S.filter (fun f => f.IsRoot c)).card := by
  simp only [rts, Finset.card_filter]
  exact Finset.sum_comm
end PI.SqfDivDeg.W
