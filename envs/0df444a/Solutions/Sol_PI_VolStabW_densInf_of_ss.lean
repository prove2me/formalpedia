-- Prove2me | solution 1 for PI.VolStabW.densInf_of_ss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:16:07.826152+00:00
-- url     : https://prove2.me/submissions/8e1d0e10-1944-4fca-88cb-d404340cb9c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfCo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfFS
import Theorems.Thm_PI_VolStabW_freeSurj_of
import Theorems.Thm_PI_VolStabW_densInf_of_tens


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
theorem _root_.solution (h2 : TensR) (h3 : SemisimpleTens) : DensInf :=
  densInf_of_tens h2 (freeSurj_of h3)
end PI.VolStabW
