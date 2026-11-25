-- Prove2me | solution 1 for PI.SqfDivDeg.W.sum_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:59.644543+00:00
-- url     : https://prove2.me/submissions/f48cc5a1-8893-4cd6-a76e-8c70475b3045

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
    ∑ f ∈ S, (rts f).offDiag.card =
      ∑ x ∈ (univ : Finset (ZMod g)).offDiag,
        (S.filter (fun f => f.IsRoot x.1 ∧ f.IsRoot x.2)).card := by
  have hs : ∀ f : (ZMod g)[X], (rts f).offDiag =
      (univ : Finset (ZMod g)).offDiag.filter (fun x => f.IsRoot x.1 ∧ f.IsRoot x.2) := by
    intro f
    ext x
    simp only [rts, Finset.mem_offDiag, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  simp only [hs, Finset.card_filter]
  exact Finset.sum_comm
end PI.SqfDivDeg.W
