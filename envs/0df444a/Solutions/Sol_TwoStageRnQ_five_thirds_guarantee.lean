-- Prove2me | solution 1 for TwoStageRnQ.five_thirds_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T00:33:58.975206+00:00
-- url     : https://prove2.me/submissions/f6b641ed-8737-4c9b-b55c-61a77b5017bc

import Theorems.Thm_TwoStageRnQ_classical_le_Jjoint
import Theorems.Thm_TwoStageRnQ_cancellation
import Theorems.Thm_TwoStageRnQ_classical_ship_le_lot
import Theorems.Thm_TwoStageRnQ_two_lower_bounds
import Theorems.Thm_TwoStageRnQ_cost_order
import Theorems.Thm_TwoStageRnQ_classical_attained
import Mathlib.Tactic.Linarith

/-!
Assembly of Theorem 1 (eq. (20)) from `classical_le_Jjoint`,
`cancellation` (eq. (27)), `classical_ship_le_lot`, `two_lower_bounds` (Proposition 2),
`cost_order` (eq. (5)) and `classical_attained` (Appendix D.5).
-/

namespace TwoStageRnQ

theorem _root_.solution (P : Params) (S : DemandSpace P) :
    (⨅ c : ClassicalControls, classicalLotCost P S c) ≤ ENNReal.ofReal (5 / 3 * P.Ltwo) ∧
    (⨅ c : ClassicalControls, classicalShipCost P S c) ≤ ENNReal.ofReal (5 / 3 * P.Ltwo) ∧
    P.Ltwo ≤ P.LBsp ∧
    ENNReal.ofReal P.LBsp ≤ OPTsh P ∧
    OPTsh P ≤ OPTlot P ∧
    (0 < P.lam → 0 < P.h1 → 0 < P.h2 → 0 < P.p →
      ∃ c : ClassicalControls, c.1.2.2.2.2 = 0 ∧
        classicalLotCost P S c ≤ ENNReal.ofReal (5 / 3 * P.Ltwo)) := by
  have hJ : P.Jjoint P.k1 P.k2 ≤ 5 / 3 * P.Ltwo := by
    have := TwoStageRnQ.cancellation P
    linarith
  have hJ' : ENNReal.ofReal (P.Jjoint P.k1 P.k2) ≤ ENNReal.ofReal (5 / 3 * P.Ltwo) :=
    ENNReal.ofReal_le_ofReal hJ
  have hlot := (TwoStageRnQ.classical_le_Jjoint P S).trans hJ'
  obtain ⟨hL, hO⟩ := TwoStageRnQ.two_lower_bounds P
  refine ⟨hlot, ?_, hL, hO, TwoStageRnQ.cost_order P, ?_⟩
  · exact (iInf_mono fun c => TwoStageRnQ.classical_ship_le_lot P S c).trans hlot
  · intro hl h1 h2 hp
    obtain ⟨c, hc0, hc⟩ := TwoStageRnQ.classical_attained P hl h1 h2 hp S
    exact ⟨c, hc0, hc.trans hJ'⟩

end TwoStageRnQ
