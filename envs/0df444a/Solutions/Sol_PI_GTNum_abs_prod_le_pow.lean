-- Prove2me | solution 1 for PI.GTNum.abs_prod_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:41.776169+00:00
-- url     : https://prove2.me/submissions/00e9920e-78b7-4391-ac87-636289c2a1de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Theorems.Thm_PI_GTNum_abs_prod_le_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GTNum
open Finset
namespace PI.GTNum
theorem _root_.solution {α : Type*} (s : Finset α) (f : α → ℤ) (B : ℤ) (h : ∀ x ∈ s, |f x| ≤ B) :
    |∏ x ∈ s, f x| ≤ B ^ s.card := by
  simpa [Finset.prod_const] using abs_prod_le_prod s f (fun _ => B) h
end PI.GTNum
