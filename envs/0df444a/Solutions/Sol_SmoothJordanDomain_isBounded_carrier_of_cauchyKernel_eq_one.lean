-- Prove2me | solution 1 for SmoothJordanDomain.isBounded_carrier_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:59.824835+00:00
-- url     : https://prove2.me/submissions/d337841e-aee6-41b3-86ed-0bdd54f875cc

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanion_cocompact
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    Bornology.IsBounded Omega.carrier := by
  have hdecay :=
    tendsto_crouzeixPolynomialScalarCompanion_cocompact
      Omega (Polynomial.C 1)
  have hsmall : ∀ᶠ z : ℂ in cocompact ℂ,
      dist (crouzeixPolynomialScalarCompanion
        Omega (Polynomial.C 1) z) 0 < 1 / 2 :=
    Metric.tendsto_nhds.mp hdecay (1 / 2) (by norm_num)
  rw [Filter.eventually_iff] at hsmall
  obtain ⟨K, hKcompact, hKsub⟩ := Filter.mem_cocompact.mp hsmall
  apply hKcompact.isBounded.subset
  intro z hz
  by_contra hzK
  have hzsmall := hKsub hzK
  have hcompanion :
      crouzeixPolynomialScalarCompanion Omega (Polynomial.C 1) z = 1 := by
    simpa only [crouzeixPolynomialScalarCompanion,
      crouzeixScalarCauchyKernel, Polynomial.eval_C, star_one, one_mul] using
      hkernel z hz
  change dist (crouzeixPolynomialScalarCompanion
    Omega (Polynomial.C 1) z) 0 < 1 / 2 at hzsmall
  rw [hcompanion, dist_zero_right, norm_one] at hzsmall
  norm_num at hzsmall
end SmoothJordanDomain
