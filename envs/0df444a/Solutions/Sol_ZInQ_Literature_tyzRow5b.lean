-- Prove2me | solution 1 for ZInQ.Literature.tyzRow5b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T18:51:46.422751+00:00
-- url     : https://prove2.me/submissions/d029f6c5-9926-44d6-b2a2-aa8c43b25e70
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ZInQLiterature
import Theorems.Thm_ZInQ_Literature_heckeContinuation
import Theorems.Thm_ZInQ_Literature_tyzThm35ReadingA

theorem solution : ZInQ.Literature.TYZRow5b := by
  intro d hd hsq h5b
  have hd0 : d ≠ 0 := by omega
  obtain ⟨F, hF⟩ := ZInQ.Literature.heckeContinuation d hd0
  refine ⟨F, hF, ?_⟩
  by_contra hlt
  have h2 : 2 ≤ analyticOrderAt F 1 := by
    have := not_le.mp hlt
    exact Order.add_one_le_of_lt this
  have := (ZInQ.Literature.tyzThm35ReadingA d hd hsq F hF h2).2
  rw [h5b] at this
  exact absurd this (by decide)
