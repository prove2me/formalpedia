-- Prove2me | solution 1 for SmoothJordanDomain.exists_oriented_point_canonicalOrientation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:11.76018+00:00
-- url     : https://prove2.me/submissions/ee0d91c8-fed5-4110-a6f1-f08c3de03df2

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_deriv_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
section
open Complex Set
open scoped Real
private theorem SmoothJordanDomain.orientationPointSupport_mem
    (Omega : SmoothJordanDomain) :
    Omega.orientationPointSupport ∈ Omega.carrier :=
  Classical.choose_spec Omega.carrier_nonempty
private theorem periodic_deriv_boundaryParam_support
    (Omega : SmoothJordanDomain) :
    Function.Periodic (deriv Omega.boundaryParam) (2 * Real.pi) := by
  intro t
  have hfun : (fun x : ℝ ↦ Omega.boundaryParam (x + 2 * Real.pi)) =
      Omega.boundaryParam := by
    funext x
    exact Omega.boundaryParam_periodic x
  have h := congrArg (fun f : ℝ → ℂ ↦ deriv f t) hfun
  rwa [deriv_comp_add_const] at h
end

set_option autoImplicit false
open Complex Set
open scoped Real
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain) :
    ∃ c ∈ Omega.canonicalOrientation.carrier,
      ((starRingEnd ℂ)
          (-I * deriv Omega.canonicalOrientation.boundaryParam 0) *
        (c - Omega.canonicalOrientation.boundaryParam 0)).re ≤ 0 := by
  let c := Omega.orientationPointSupport
  have hc : c ∈ Omega.carrier := Omega.orientationPointSupport_mem
  by_cases hside :
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam 0) *
        (c - Omega.boundaryParam 0)).re ≤ 0
  · have horient : Omega.canonicalOrientation = Omega := by
      simp only [SmoothJordanDomain.canonicalOrientation, c, hside, if_pos]
    rw [horient]
    exact ⟨c, hc, hside⟩
  · have hpos : 0 <
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam 0) *
          (c - Omega.boundaryParam 0)).re := lt_of_not_ge hside
    have horient : Omega.canonicalOrientation = Omega.reverseOrientation := by
      simp only [SmoothJordanDomain.canonicalOrientation, c, hside, if_false]
    rw [horient]
    refine ⟨c, by simpa only [reverseOrientation_carrier] using hc, ?_⟩
    rw [deriv_reverseOrientation_boundaryParam,
      reverseOrientation_boundaryParam, sub_zero]
    have hderivT : deriv Omega.boundaryParam (2 * Real.pi) =
        deriv Omega.boundaryParam 0 := by
      simpa only [zero_add] using periodic_deriv_boundaryParam_support Omega 0
    rw [hderivT]
    rw [show Omega.boundaryParam (2 * Real.pi) =
        Omega.boundaryParam 0 by
      simpa only [zero_add] using Omega.boundaryParam_periodic 0]
    have hcomplex :
        (starRingEnd ℂ) (-I * -deriv Omega.boundaryParam 0) *
            (c - Omega.boundaryParam 0) =
          -((starRingEnd ℂ) (-I * deriv Omega.boundaryParam 0) *
            (c - Omega.boundaryParam 0)) := by
      simp only [map_mul, map_neg]
      ring
    rw [hcomplex, neg_re]
    exact neg_nonpos.mpr hpos.le
end SmoothJordanDomain
