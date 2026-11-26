-- Prove2me | solution 1 for SmoothJordanDomain.boundaryParam_mem_resolventSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:13.303109+00:00
-- url     : https://prove2.me/submissions/4a6103f4-0bdd-40dd-8997-721ff94aa1b3

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Crouzeix_AuxOperator
import Theorems.Thm_spectrum_subset_closure_numericalRange

section
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace SmoothJordanDomain
private theorem boundaryParam_mem_frontier (Omega : SmoothJordanDomain) (t : ℝ) :
    Omega.boundaryParam t ∈ frontier Omega.carrier := by
  rw [← Omega.boundaryParam_range]
  exact ⟨t, rfl⟩
end SmoothJordanDomain
end

set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
open SmoothJordanDomain
namespace SmoothJordanDomain
theorem _root_.solution [CompleteSpace E]
    (Omega : SmoothJordanDomain) (A : E →L[ℂ] E)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) (t : ℝ) :
    Omega.boundaryParam t ∈ resolventSet ℂ A := by
  by_contra hrho
  have hsigma : Omega.boundaryParam t ∈ spectrum ℂ A := hrho
  have hcarrier := hOmega (spectrum_subset_closure_numericalRange A hsigma)
  have hfrontier := boundaryParam_mem_frontier Omega t
  have hempty : Omega.boundaryParam t ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hcarrier, hfrontier⟩
  exact hempty
end SmoothJordanDomain
