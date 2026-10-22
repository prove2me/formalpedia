-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.lerP
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:28:24.531123+00:00
-- url     : https://prove2.me/submissions/022bfd80-ce3e-474a-bb25-f3368778009f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Dependency50.P27 in
theorem solution {R : Type*} [CommRing R] [IsDomain R]
    [LinearOrder R] [IsStrictOrderedRing R] (x y : R) :
    LerXorGtr x y (decide (x ≤ y)) (decide (y < x)) := by
  by_cases h : x ≤ y
  · have h' : ¬ y < x := not_lt.mpr h
    simp only [h, h', decide_true, decide_false]
    exact LerXorGtr.lerNotGtr h
  · have h' : y < x := not_le.mp h
    simp only [h, h', decide_true, decide_false]
    exact LerXorGtr.gtrNotLer h'
