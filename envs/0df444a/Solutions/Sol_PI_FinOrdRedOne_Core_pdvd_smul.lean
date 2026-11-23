-- Prove2me | solution 1 for PI.FinOrdRedOne.Core.pdvd_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:31.978031+00:00
-- url     : https://prove2.me/submissions/6c47d815-2258-46dd-9d26-1be30545d64e

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
theorem _root_.solution {q : R} {k : ℕ} {A : Matrix n n R} (c : R) (hA : PDvd q k A) :
    PDvd q k (c • A) := by
  obtain ⟨X, rfl⟩ := hA
  exact ⟨c • X, by rw [smul_comm]⟩
end PI.FinOrdRedOne.Core
