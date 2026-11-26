-- Prove2me | solution 1 for commute_resolvent_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:59.427667+00:00
-- url     : https://prove2.me/submissions/62bddc78-f8a7-40f5-802d-325c9704a481

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy

set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution
    (B D : E →L[ℂ] E) (z : ℂ) (hDB : Commute D B)
    (hres : z ∈ resolventSet ℂ B) :
    Commute D (resolvent B z) := by
  rw [spectrum.resolvent_eq hres]
  apply Commute.units_inv_right
  rw [hres.unit_spec]
  exact (Algebra.commute_algebraMap_right z D).sub_right hDB
