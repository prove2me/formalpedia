-- Prove2me | solution 1 for PI.GTNum.abs_prod_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:01.170797+00:00
-- url     : https://prove2.me/submissions/88f96a3d-4739-45bf-83c1-211501ffc70f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin

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
theorem _root_.solution {α : Type*} (s : Finset α) (f b : α → ℤ) (h : ∀ x ∈ s, |f x| ≤ b x) :
    |∏ x ∈ s, f x| ≤ ∏ x ∈ s, b x := by
  rw [abs_prod]
  exact Finset.prod_le_prod (fun x _ => abs_nonneg _) h
end PI.GTNum
