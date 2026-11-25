-- Prove2me | solution 1 for PI.AmpRootJacW.mp_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:18.757617+00:00
-- url     : https://prove2.me/submissions/81bad813-fee7-4d47-89b0-b41a23f3593f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.AmpRootJacW
variable {n : ℕ}
namespace PI.AmpRootJacW
theorem _root_.solution {ι : Type} [Fintype ι] (τ : ι ≃ ι) :
    MeasurePreserving (fun (w : ι → ℂ) i => w (τ i)) volume volume := by
  have h := MeasureTheory.volume_preserving_arrowCongr' τ.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)
  convert h using 1
  all_goals first
    | rfl
    | (funext w i; simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr'])
end PI.AmpRootJacW
