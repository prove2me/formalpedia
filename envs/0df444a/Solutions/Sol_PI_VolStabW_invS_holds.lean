-- Prove2me | solution 1 for PI.VolStabW.invS_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:16:19.838861+00:00
-- url     : https://prove2.me/submissions/1dbae459-7cd8-4d51-b969-65f7bae6f96d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_InvInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnimodStab
import Theorems.Thm_PI_VolStabW_us_invInv
import Theorems.Thm_PI_VolStabW_us_isClosed_stab
import Theorems.Thm_PI_VolStabW_unimodStab_holds
import Theorems.Thm_PI_VolStabW_um_sigmaCompact_HA


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
theorem _root_.solution : InvS := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ' hC
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J hSWa1
  have hcl := us_isClosed_stab F E σ M a J X0
  have : LocallyCompactSpace (stabT (AF F) σ J X0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SigmaCompactSpace (stabT (AF F) σ J X0) := hcl.sigmaCompactSpace
  have : IsMulRightInvariant μ' :=
    unimodStab_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ' hC
  exact us_invInv μ'
end PI.VolStabW
