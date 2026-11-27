-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.ModW.onG_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:15:18.440349+00:00
-- url     : https://prove2.me/submissions/d250f534-131b-4d0f-8290-9229810c6c94

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_map_onG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI
variable {m : ℕ}
variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
open MG
namespace PI.QuotSetU.UnitaryGroupMassFormula.ModW
theorem _root_.solution (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) : onG hG μ ≠ 0 := by
  intro h
  have e := map_onG (hG := hG) μ hμ
  rw [h, Measure.map_zero] at e
  exact hμ.2.1 e.symm
end PI.QuotSetU.UnitaryGroupMassFormula.ModW
