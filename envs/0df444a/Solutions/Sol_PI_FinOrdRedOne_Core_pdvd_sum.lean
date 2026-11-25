-- Prove2me | solution 1 for PI.FinOrdRedOne.Core.pdvd_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:46:57.583802+00:00
-- url     : https://prove2.me/submissions/c1c15059-3b7e-4b70-8b22-ce2abc75ead3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
import Theorems.Thm_PI_FinOrdRedOne_Core_pdvd_add
import Theorems.Thm_PI_FinOrdRedOne_Core_pdvd_zero

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
theorem _root_.solution {q : R} {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Matrix n n R)
    (h : ∀ i ∈ s, PDvd q k (f i)) : PDvd q k (∑ i ∈ s, f i) :=
  Finset.sum_induction f (PDvd q k) (fun _ _ ha hb => pdvd_add ha hb) (pdvd_zero q k) h
end PI.FinOrdRedOne.Core
