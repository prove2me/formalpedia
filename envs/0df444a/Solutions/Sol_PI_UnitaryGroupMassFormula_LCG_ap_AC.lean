-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_AC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:52.792724+00:00
-- url     : https://prove2.me/submissions/d7191cb1-8122-4e8c-a22d-72e9a4e13756

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_amat_coord
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
theorem _root_.solution (x y : I.GA) (v : InfinitePlace I.F) (δ : Matrix (Fin I.n) (Fin I.n) I.E) {k : ℕ}
    (u : Fin k → Fin I.n → I.E) :
    amat I x y v δ * colM I y v u = colM I x v (fun c => δ *ᵥ u c) := by
  ext i c
  simp only [colM, Matrix.of_apply]
  rw [← ap_amat_coord I x y v δ (u c)]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
end PI.UnitaryGroupMassFormula.LCG
