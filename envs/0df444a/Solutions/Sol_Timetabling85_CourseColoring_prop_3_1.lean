-- Prove2me | solution 1 for Timetabling85.CourseColoring.prop_3_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:02:10.220021+00:00
-- url     : https://prove2.me/submissions/e3c74fa0-aa79-4edf-8aa1-0ddda5176656

import Theorems.Thm_Timetabling85_CourseColoring_coloring_interpretation

open Timetabling85.CourseColoring

theorem solution {q r p : ℕ} (P : CSUP q r p) :
    (∃ s : P.Lecture → Fin p, P.IsFeasible s) ↔ P.csupGraph.Colorable p := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨c, _⟩ := (coloring_interpretation P).2 s hs
    exact ⟨c⟩
  · rintro ⟨c⟩
    obtain ⟨s, hs, _⟩ := (coloring_interpretation P).1 c
    exact ⟨s, hs⟩
