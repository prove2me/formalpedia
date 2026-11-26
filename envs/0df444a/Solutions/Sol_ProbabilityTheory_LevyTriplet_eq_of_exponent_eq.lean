-- Prove2me | solution 1 for ProbabilityTheory.LevyTriplet.eq_of_exponent_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:34:09.334688+00:00
-- url     : https://prove2.me/submissions/d6b1f86b-8243-4e06-8593-4cb097fe85e8

import Definitions.Def_SourceProof_1a692c64413256141ec63577

open ProbabilityTheory Filter MeasureTheory
open scoped ENNReal NNReal Topology

theorem solution {η ξ : LevyTriplet} (h : η.exponent = ξ.exponent) : η = ξ := by
  exact Prove2MeSourceProof.h_1a692c64413256141ec63577 h
