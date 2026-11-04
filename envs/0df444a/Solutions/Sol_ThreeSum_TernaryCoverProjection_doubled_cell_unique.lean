-- Prove2me | solution 1 for ThreeSum.TernaryCoverProjection.doubled_cell_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:54:52.363683+00:00
-- url     : https://prove2.me/submissions/b4b484d7-af9d-4f8d-b7cb-b8765a93dbc6

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal
namespace ThreeSum.TernaryCoverProjection
theorem _root_.solution (swap : Bool) (a b c d : Fin 3)
    (hab : a.val + b.val ≤ 2) (hcd : c.val + d.val ≤ 2)
    (heq : doubledCode swap a b = doubledCode swap c d)
    (hmark : doubledMark swap a b ↔ doubledMark swap c d) :
    a = c ∧ b = d := by
  cases swap <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [doubledCode, doubledMark, Fin.ext_iff] at *
end ThreeSum.TernaryCoverProjection
