-- Prove2me | solution 1 for PI.VolStabSW.densInf_of_ss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:46.638081+00:00
-- url     : https://prove2.me/submissions/bce64ed8-e04e-496f-a776-a381b2337797

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfCo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfFS
import Theorems.Thm_PI_VolStabSW_freeSurj_of
import Theorems.Thm_PI_VolStabSW_densInf_of_tens


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
theorem _root_.solution (h2 : TensR) (h3 : SemisimpleTens) : DensInf :=
  densInf_of_tens h2 (freeSurj_of h3)
end PI.VolStabSW
