-- Prove2me | solution 1 for PI.FinOrdRedOne.Core.pdvd_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:36.227842+00:00
-- url     : https://prove2.me/submissions/dd93a8f8-9ec5-43e9-8bc1-58d268e04b3e

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
theorem _root_.solution {q : R} {k m : ℕ} (h : m ≤ k) {A : Matrix n n R} (hA : PDvd q k A) :
    PDvd q m A := by
  obtain ⟨X, rfl⟩ := hA
  refine ⟨q ^ (k - m) • X, ?_⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' h]
end PI.FinOrdRedOne.Core
