-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.hform_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:17.595168+00:00
-- url     : https://prove2.me/submissions/ad899b6d-1e6d-44a2-ad47-fe0c2b390f0c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexOf
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable {E : Type} [Field E] [StarRing E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (J : Matrix (Fin n) (Fin n) E) (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (w z : Fin n → E) :
    starRingEnd E (Formalism.UG.hform (starRingEnd E) J w z) = Formalism.UG.hform (starRingEnd E) J z w := by
  have hJ' : ∀ i j, starRingEnd E (J i j) = J j i := by
    intro i j
    have := congrFun (congrFun hJ j) i
    simpa [Formalism.UG.cT] using this
  unfold Formalism.UG.hform
  simp only [map_sum, map_mul, starRingEnd_self_apply, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring
end PI.UnitaryGroupMassFormula.LCG
