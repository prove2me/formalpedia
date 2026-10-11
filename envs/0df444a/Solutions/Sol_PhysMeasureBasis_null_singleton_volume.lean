-- Prove2me | solution 1 for PhysMeasureBasis.null_singleton_volume
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:59:50.927639+00:00
-- url     : https://prove2.me/submissions/dcb102ad-9d56-4f3a-b39f-c17d56e368d2

-- Generated from PhysMeasureBasis.lean — solution of PhysMeasureBasis.null_singleton_volume
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis



open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (y : ℝ) : volume ({y} : Set ℝ) = 0 := by

  norm_num +zetaDelta at *
