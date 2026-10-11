-- Prove2me | solution 1 for WeilDefect.RPB108.completed_column_identity
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:54:44.530463+00:00
-- url     : https://prove2.me/submissions/e5602b5c-4067-46f2-b9c2-50520a13f8ae

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (T : E →L[ℂ] E) (x source : Fin 4 → E)
    (z : Fin 4 → ℂ) (h : E) :
    (∑ i, z i • (x i-T (source i)))+h =
      (∑ i, z i • x i)+(h-T (∑ i, z i • source i)) := by
  simp only [smul_sub, Finset.sum_sub_distrib, map_sum, map_smul]
  abel
