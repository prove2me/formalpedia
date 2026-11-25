-- Prove2me | solution 1 for PI.FinOrdRedOne.Core.pdvd_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:39.966309+00:00
-- url     : https://prove2.me/submissions/a1b42ab8-bc18-4111-9cfc-220dea745636

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinOrdRedOne PI.FinOrdRedOne.Core
open Matrix Finset
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace PI.FinOrdRedOne.Core
theorem _root_.solution {q : R} {k : ℕ} {A : Matrix n n R} (hA : PDvd q k A) : PDvd q k (-A) := by
  obtain ⟨X, rfl⟩ := hA
  exact ⟨-X, by rw [smul_neg]⟩
end PI.FinOrdRedOne.Core
