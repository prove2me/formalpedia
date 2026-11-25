-- Prove2me | solution 1 for PI.VolStabSW.densV_of_cos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:28.096405+00:00
-- url     : https://prove2.me/submissions/3f160112-ccf6-4215-b609-6baf31281881

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVSt
import Theorems.Thm_PI_VolStabSW_densV_of
import Theorems.Thm_PI_VolStabSW_densVLC_of

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution (hT : TensAll) (hNA : TensNA) (hC : DensVCs) : DensV :=
  densV_of hT hNA (densVLC_of hT hNA hC)
end PI.VolStabSW
