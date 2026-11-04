-- Prove2me | solution 1 for ThreeSum.TernaryTypeCardinality.positions_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:53.954176+00:00
-- url     : https://prove2.me/submissions/b4124c87-402d-4481-bd35-0e12e1f8b5f4

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryTypeCardinality
theorem _root_.solution {L : ℕ} (w : TritWord L) :
    Disjoint (positions w 2) (positions w 1) := by
  apply Finset.disjoint_left.mpr
  intro i hi2 hi1
  have h2 : w i=2 := (mem_filter.mp hi2).2
  have h1 : w i=1 := (mem_filter.mp hi1).2
  have hh : (2 : Fin 3)=1 := h2.symm.trans h1
  norm_num [Fin.ext_iff] at hh
end ThreeSum.TernaryTypeCardinality
