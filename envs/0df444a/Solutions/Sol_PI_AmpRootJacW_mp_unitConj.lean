-- Prove2me | solution 1 for PI.AmpRootJacW.mp_unitConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:38.141443+00:00
-- url     : https://prove2.me/submissions/998a0e2a-2c0b-49f2-8cba-6b35a475b4e9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero
import Theorems.Thm_PI_AmpRootJacW_mp_reindex
import Theorems.Thm_PI_AmpRootJacW_mp_unitConj1

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
theorem _root_.solution {ι : Type} [Fintype ι] (τ : ι ≃ ι) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1) :
    MeasurePreserving (fun (w : ι → ℂ) i => c i * star (w (τ i))) volume volume := by
  have h1 : MeasurePreserving (fun (x : ι → ℂ) i => c i * star (x i)) volume volume :=
    MeasureTheory.volume_preserving_pi (fun i => mp_unitConj1 (c i) (hc i))
  exact h1.comp (mp_reindex τ)
end PI.AmpRootJacW
