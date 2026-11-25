-- Prove2me | solution 1 for PI.VolStabW.invInv_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:56.50101+00:00
-- url     : https://prove2.me/submissions/082d0764-e366-4b4d-ac9d-aaaace6957ba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_InvInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnimodStab
import Theorems.Thm_PI_VolStabW_invG_holds
import Theorems.Thm_PI_VolStabW_invS_holds

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
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolFromSW PI.AdicCompletionValuation NumberField
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution : InvInv := fun F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet =>
  ⟨invG_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet,
    invS_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet⟩
end PI.VolStabW
