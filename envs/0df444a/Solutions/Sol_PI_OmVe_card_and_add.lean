-- Prove2me | solution 1 for PI.OmVe.card_and_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:01:01.187992+00:00
-- url     : https://prove2.me/submissions/92ac29ad-a7c5-4cb1-be8a-c348d5b5d7d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_SingleMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_CardAndAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
namespace PI.OmVe
theorem _root_.solution {α : Type} [Finite α] (G Q : α → Prop) :
    Nat.card {x // G x ∧ Q x} + Nat.card {x // G x ∧ ¬ Q x} = Nat.card {x // G x} := by
  classical
  rw [← Nat.card_sum]
  exact Nat.card_congr
    (((Equiv.subtypeSubtypeEquivSubtypeInter G Q).symm.sumCongr
      (Equiv.subtypeSubtypeEquivSubtypeInter G (fun x => ¬ Q x)).symm).trans
      (Equiv.sumCompl (fun y : {x // G x} => Q y.1)))
end PI.OmVe
