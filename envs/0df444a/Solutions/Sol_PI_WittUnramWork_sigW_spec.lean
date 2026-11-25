-- Prove2me | solution 1 for PI.WittUnramWork.sigW_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:23:00.032246+00:00
-- url     : https://prove2.me/submissions/625abf27-a0f9-4b66-a089-468f403449aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WittUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_GhostComponentG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WittUnramWork
open WittVector Finset
variable {p : ℕ} [hp : Fact p.Prime] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
namespace PI.WittUnramWork
theorem _root_.solution (hinj : Function.Injective (algebraMap W Qq)) (σ : Qq ≃+* Qq)
    (hσ : ∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) (x : W) :
    algebraMap W Qq (sigW hinj σ hσ x) = σ (algebraMap W Qq x) := sigF_spec σ hσ x
end PI.WittUnramWork
