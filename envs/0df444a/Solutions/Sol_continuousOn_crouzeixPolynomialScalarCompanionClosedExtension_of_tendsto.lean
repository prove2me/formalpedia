-- Prove2me | solution 1 for continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:10:29.924906+00:00
-- url     : https://prove2.me/submissions/1df7da17-fa5e-4859-bee5-7c9debb30d49

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Theorems.Thm_analyticOn_crouzeixPolynomialScalarCompanion


set_option autoImplicit false
open Complex Filter Set
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (b : ℂ → ℂ)
    (hlim : ∀ z ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanion Omega p)
        (nhdsWithin z Omega.carrier) (nhds (b z))) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      (closure Omega.carrier) := by
  apply continuousOn_extendFrom (fun _ hz ↦ hz)
  intro z hz
  rw [closure_eq_self_union_frontier] at hz
  rcases hz with hz | hz
  · exact ⟨crouzeixPolynomialScalarCompanion Omega p z,
      (analyticOn_crouzeixPolynomialScalarCompanion Omega p).continuousOn z hz⟩
  · exact ⟨b z, hlim z hz⟩
