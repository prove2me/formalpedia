-- Prove2me | solution 1 for PI.VolStabW.invG_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:04.959798+00:00
-- url     : https://prove2.me/submissions/f9734532-1409-4fb4-b4b7-06bb69b29ea4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_InvInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnimodStab
import Theorems.Thm_PI_VolStabW_us_invInv
import Theorems.Thm_PI_VolStabW_um_sigmaCompact_HA
import Theorems.Thm_PI_VolStabW_unimod_holds


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
theorem _root_.solution : InvG := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 _a ha1 ha2 X0 hT hdet μ hμ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have : μ.IsHaarMeasure := hμ
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J hSWa1
  have : IsMulRightInvariant μ :=
    unimod_holds F E σ hσ M J hJ hSWa1 hSWc1 _a ha1 ha2 X0 hT hdet μ hμ
  exact us_invInv μ
end PI.VolStabW
