-- Prove2me | solution 1 for Timetabling85.CourseColoring.figure4_feasible
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:00:31.820994+00:00
-- url     : https://prove2.me/submissions/b79c4e66-c183-47c2-ac01-689e17c7506f

import Definitions.Def_Timetabling85_CourseColoring_Figure4

open Timetabling85.CourseColoring

theorem solution : figure4.IsFeasibleSchedule 4 figure4Schedule := by
  unfold CourseInstance.IsFeasibleSchedule
  decide
