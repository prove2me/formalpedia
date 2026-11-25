-- Prove2me | solution 1 for PI.WfSubstProof.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:48.5448+00:00
-- url     : https://prove2.me/submissions/d594b337-461d-42ae-ace0-16fbb9b44f4b

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
theorem _root_.solution {A : Type} [CommRing A] (S : Subring A) {σ : Type} (f : MvPowerSeries σ A)
    (h : ∀ e, MvPowerSeries.coeff e f ∈ S) :
    ∃ g : MvPowerSeries σ S, MvPowerSeries.map S.subtype g = f := by
  let g : MvPowerSeries σ S := fun e => ⟨MvPowerSeries.coeff e f, h e⟩
  refine ⟨g, ?_⟩
  ext e
  rw [MvPowerSeries.coeff_map]
  rfl
end PI.WfSubstProof
