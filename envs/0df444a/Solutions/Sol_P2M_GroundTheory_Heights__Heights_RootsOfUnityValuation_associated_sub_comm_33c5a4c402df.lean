-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootsOfUnityValuation_associated_sub_comm_33c5a4c402df
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:14:45.470163+00:00
-- url     : https://prove2.me/submissions/ae34031f-e1ae-4cf1-b5a4-0995bbf22cdb

import Mathlib
variable {A : Type*} [CommRing A]


theorem solution (a b : A) : Associated (a - b) (b - a) := by
  refine ⟨-1, ?_⟩; simp
