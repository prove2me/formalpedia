-- Prove2me | solution 1 for SethiChengSS.Finite.proposition_4_1_iv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T13:42:18.70388+00:00
-- url     : https://prove2.me/submissions/67ce1ebf-1c92-4007-a446-c234494a8cac

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Finite_KConvexity

set_option autoImplicit false
set_option linter.all false

open SethiChengSS SethiChengSS.Finite in open MeasureTheory Filter Topology in
theorem solution (K : ℝ) (g : ℝ → ℝ) (D : Set ℝ) (hK : 0 ≤ K)
    (hg : BertsekasKConvex K g) (hD : Convex ℝ D) : KConvexOn K D g := by
  intros
  tauto
