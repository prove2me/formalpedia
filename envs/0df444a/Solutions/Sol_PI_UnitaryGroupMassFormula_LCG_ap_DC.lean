-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ap_DC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:45:39.379301+00:00
-- url     : https://prove2.me/submissions/38989a23-3f11-4b02-8b81-a144b3194001

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_Jm_herm
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_coordV
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_pair
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_form
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_entry
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
theorem _root_.solution (y : I.GA) (v : InfinitePlace I.F) {k : ℕ} (b' u : Fin k → Fin I.n → I.E) :
    (Formalism.REAL.Jm (I.ε v) * colM I y v b')ᴴ * colM I y v u = (pairM I b' u).map (I.φ v) := by
  rw [Matrix.conjTranspose_mul, ap_Jm_herm]
  ext a c
  rw [ap_entry, Matrix.map_apply]
  have e1 : (fun i => colM I y v b' i a) = PI.LatCountG.coordV I y v (b' a) := rfl
  have e2 : (fun i => colM I y v u i c) = PI.LatCountG.coordV I y v (u c) := rfl
  rw [e1, e2, ap_coordV, ap_coordV, ap_pair]
  simp only [pairM, Matrix.of_apply]
  rw [ap_form]
end PI.UnitaryGroupMassFormula.LCG
