-- Prove2me | solution 1 for PI.JetsPhW.Ch.degree_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:44:20.500711+00:00
-- url     : https://prove2.me/submissions/17293f16-1ce2-4fe6-856f-ce4273e9e163

import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffPowEqZeroOfDegreeLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI.JetsPhW
open PI PI.JetsPhW PI.JetsPhW.Ch
variable {R : Type*} [CommRing R] {σ : Type*}
namespace PI.JetsPhW.Ch
theorem _root_.solution {y e : σ →₀ ℕ} (h : y ≤ e) : y.degree ≤ e.degree := by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  rw [map_add]
  exact Nat.le_add_right _ _
end PI.JetsPhW.Ch
