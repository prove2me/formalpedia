-- Prove2me | solution 1 for PI.FinOrdRedOne.Core.pdvd_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:16.498736+00:00
-- url     : https://prove2.me/submissions/22d944dc-9b63-44a4-a68e-3115f21c9e3f

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
theorem _root_.solution {q : R} {k : ℕ} {A B : Matrix n n R} (hA : PDvd q k A) (hB : PDvd q k B) :
    PDvd q k (A + B) := by
  obtain ⟨X, rfl⟩ := hA
  obtain ⟨Y, rfl⟩ := hB
  exact ⟨X + Y, by rw [smul_add]⟩
end PI.FinOrdRedOne.Core
