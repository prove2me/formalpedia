-- Prove2me | solution 1 for RiemannMasullo.locallyCompactSpace_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:48:08.74942+00:00
-- url     : https://prove2.me/submissions/7d651aef-bffa-40b4-b20d-70096fa323a9

-- Adapted from mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/ForMathlib/NumberTheory/NumberField/Completion/FinitePlace.lean#L70-L73
import Theorems.Thm_RiemannMasullo_properSpace_adicCompletion
import Mathlib
import Definitions.Def_RiemannMasullo_AdicCompletionNorm

open scoped RiemannMasullo.AdicCompletionNorm
open Valued.integer

open Filter IsDedekindDomain IsLocalRing Topology
open scoped WithZero
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  [Field K] [Algebra R K] [IsFractionRing R K]

theorem solution (v : HeightOneSpectrum R) :
    LocallyCompactSpace (v.adicCompletion K) := by
  let := RiemannMasullo.properSpace_adicCompletion v (K := K)
  infer_instance

