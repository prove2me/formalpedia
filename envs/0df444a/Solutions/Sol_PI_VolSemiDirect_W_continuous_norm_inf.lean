-- Prove2me | solution 1 for PI.VolSemiDirect.W.continuous_norm_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:26.639261+00:00
-- url     : https://prove2.me/submissions/f371bd7e-c51e-415a-991d-7c219a878206

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct Matrix
variable (F : Type) [Field F] [NumberField F]
namespace PI.VolSemiDirect.W
theorem _root_.solution : Continuous fun y : InfiniteAdeleRing F => ‖y‖ := by
  show Continuous fun y : InfiniteAdeleRing F => ∏ v, ‖y v‖ ^ v.mult
  exact continuous_finsetProd _ fun v _ => ((continuous_apply v).norm).pow _
end PI.VolSemiDirect.W
