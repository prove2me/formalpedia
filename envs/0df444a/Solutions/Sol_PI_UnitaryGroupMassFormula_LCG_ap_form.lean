-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:21.626014+00:00
-- url     : https://prove2.me/submissions/eaf26722-899c-4b36-8fce-6daea8f63cf1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_star
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
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (v : InfinitePlace I.F) (w z : Fin I.n → I.E) :
    I.φ v (hf I w z) = star (phv I v w) ⬝ᵥ (I.J.map (I.φ v) *ᵥ phv I v z) := by
  simp only [hf, Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, phv, Pi.star_apply,
    Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply, ap_star]
  ring
end PI.UnitaryGroupMassFormula.LCG
