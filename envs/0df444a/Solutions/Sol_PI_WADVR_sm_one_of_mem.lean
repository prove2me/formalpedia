-- Prove2me | solution 1 for PI.WADVR.sm_one_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:05:57.728249+00:00
-- url     : https://prove2.me/submissions/c111dd10-4595-4b2c-9dd7-141e4086d806

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WADVR
variable {W Q : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q]
variable {ϖ : W}
namespace PI.WADVR
theorem _root_.solution (hϖ : Irreducible ϖ) {w : W} (hw : w ∈ IsLocalRing.maximalIdeal W) :
    Sm Q ϖ 1 (algebraMap W Q w) := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton'] at hw
  obtain ⟨c, rfl⟩ := hw
  exact ⟨c, by rw [zpow_one, map_mul]; ring⟩
end PI.WADVR
