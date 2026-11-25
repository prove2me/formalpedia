-- Prove2me | solution 1 for PI.VolStabW.densInf_of_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:25.876802+00:00
-- url     : https://prove2.me/submissions/6131f8c6-e3af-479e-a400-41f91432f13c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfCo
import Theorems.Thm_PI_VolStabW_quadCoord_holds
import Theorems.Thm_PI_VolStabW_coordInf_of
import Theorems.Thm_PI_VolStabW_densInf_of_coord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
open PI.AdicCompletionValuation
namespace PI.VolStabW
theorem _root_.solution (h2 : TensR) (h3 : FreeSurj) : DensInf :=
  densInf_of_coord (coordInf_of quadCoord_holds h2 h3)
end PI.VolStabW
