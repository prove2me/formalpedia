-- Prove2me | solution 1 for borelAlgebraEuclidean_eq_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:59:34.990643+00:00
-- url     : https://prove2.me/submissions/958d634e-1ef8-4350-ae03-e88709ddbb58

import Theorems.Thm_euclideanOpenBalls_generateFrom_eq_borel
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F001
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory MeasurableSpace
open scoped Pointwise

theorem solution (d : ℕ) :
    borelAlgebraEuclidean d = borel (EuclideanSpace ℝ (Fin d)) := by
  simpa [borelAlgebraEuclidean, generatedSigmaField] using
    euclideanOpenBalls_generateFrom_eq_borel d
