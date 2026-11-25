-- Prove2me | solution 1 for PI.VolStabSW.densInf_of_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:00.475828+00:00
-- url     : https://prove2.me/submissions/5504c133-95d5-4221-ae68-64dbba96ff36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfCo
import Theorems.Thm_PI_VolStabSW_quadCoord_holds
import Theorems.Thm_PI_VolStabSW_coordInf_of
import Theorems.Thm_PI_VolStabSW_densInf_of_coord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
open PI.AdicCompletionValuation
namespace PI.VolStabSW
theorem _root_.solution (h2 : TensR) (h3 : FreeSurj) : DensInf := by
  exact densInf_of_coord (coordInf_of quadCoord_holds h2 h3)
end PI.VolStabSW
