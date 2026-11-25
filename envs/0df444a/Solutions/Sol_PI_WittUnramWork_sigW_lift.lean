-- Prove2me | solution 1 for PI.WittUnramWork.sigW_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:20:30.722739+00:00
-- url     : https://prove2.me/submissions/6b120a5b-9c88-4458-b285-a1f3e41d360c

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
    ∃ y : W, sigW hinj σ hσ x = x ^ p + (p : W) * y := ⟨(hσ x).choose, rfl⟩
end PI.WittUnramWork
