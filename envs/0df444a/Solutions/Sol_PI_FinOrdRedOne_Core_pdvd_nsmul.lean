-- Prove2me | solution 1 for PI.FinOrdRedOne.Core.pdvd_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:41.627004+00:00
-- url     : https://prove2.me/submissions/c6533d56-fd78-48ae-a4c7-7c05a4e12a49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
import Theorems.Thm_PI_FinOrdRedOne_Core_pdvd_smul

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
theorem _root_.solution {q : R} {k : ℕ} {A : Matrix n n R} (c : ℕ) (hA : PDvd q k A) :
    PDvd q k (c • A) := by
  rw [← Nat.cast_smul_eq_nsmul R]
  exact pdvd_smul _ hA
end PI.FinOrdRedOne.Core
