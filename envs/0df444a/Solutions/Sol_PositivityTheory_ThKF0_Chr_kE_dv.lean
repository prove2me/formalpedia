-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.kE_dv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:41.378837+00:00
-- url     : https://prove2.me/submissions/0f5b933d-f4f2-4459-a3f0-635078d90d9c

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ κ₁ : Type}
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution (p : κ → Prop) [DecidablePred p] (w w' : V R κ) : kE R p (dv w w') =
    (Sum.elim (w.1 - w'.1) fun k => if p k then w.2 k - w'.2 k else w'.1 k,
      Sum.elim w.2 fun k => if p k then -w'.1 k else w.2 k - w'.2 k) := by
  ext (k | k) <;> by_cases h : p k <;> simp [kE, dv, h, sub_eq_add_neg]
end PositivityTheory.ThKF0.Chr
