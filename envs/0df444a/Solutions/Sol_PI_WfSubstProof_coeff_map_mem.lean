-- Prove2me | solution 1 for PI.WfSubstProof.coeff_map_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:46.683615+00:00
-- url     : https://prove2.me/submissions/8df8ab23-189a-4314-a96b-0369d69e37f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WfSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittSubstitution_CoeffMapMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfSubstProof
namespace PI.WfSubstProof
theorem _root_.solution {A : Type} [CommRing A] (S : Subring A) {σ : Type} (g : MvPowerSeries σ S)
    (e : σ →₀ ℕ) : MvPowerSeries.coeff e (MvPowerSeries.map S.subtype g) ∈ S := by
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff e g).2
end PI.WfSubstProof
