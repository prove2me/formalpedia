-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.ModW.onG_sigmaFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:15:23.732161+00:00
-- url     : https://prove2.me/submissions/f70219ba-0afd-4c83-861e-dda216a56607

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_measEmb
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
theorem _root_.solution (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) : SigmaFinite (onG hG μ) := by
  haveI := hμ.1
  exact SigmaFinite.of_map _ (measEmb (hG := hG)).measurable.aemeasurable (by rw [map_onG μ hμ]; exact hμ.1)
end PI.QuotSetU.UnitaryGroupMassFormula.ModW
