-- Prove2me | solution 1 for PI.WADVR.Sm.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:19.518663+00:00
-- url     : https://prove2.me/submissions/cfdb8bff-a3cf-4260-956e-b4447cc3ad40

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
namespace Sm
theorem _root_.solution {k : ℤ} {a b : Q} (ha : Sm Q ϖ k a) (hb : Sm Q ϖ k b) : Sm Q ϖ k (a + b) := by
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨d, rfl⟩ := hb
  exact ⟨c + d, by rw [map_add]; ring⟩
end Sm
end PI.WADVR
