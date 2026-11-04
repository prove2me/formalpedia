-- Prove2me | solution 1 for ThreeSum.TernaryCoverProjection.cell_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:54:07.277205+00:00
-- url     : https://prove2.me/submissions/4e01be1e-540c-437c-ab83-544b3fc99c7b

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal
namespace ThreeSum.TernaryCoverProjection
theorem _root_.solution (a b c d : Fin 3)
    (hab : a.val + b.val ≤ 2) (hcd : c.val + d.val ≤ 2)
    (heq : differenceCode a b = differenceCode c d)
    (hmark : (a = 1 ∧ b = 1) ↔ (c = 1 ∧ d = 1)) :
    a = c ∧ b = d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [differenceCode] at *
end ThreeSum.TernaryCoverProjection
