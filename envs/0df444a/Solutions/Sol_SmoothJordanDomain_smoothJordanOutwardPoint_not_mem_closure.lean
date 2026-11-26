-- Prove2me | solution 1 for SmoothJordanDomain.smoothJordanOutwardPoint_not_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:14:26.352307+00:00
-- url     : https://prove2.me/submissions/7eb7214d-6518-4131-b025-764fffc9cae2

import Definitions.Def_Operator_Crouzeix_ConvexRungeIntegral
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan

set_option autoImplicit false
open Complex Filter Metric Set
open scoped Interval Real Topology
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    smoothJordanOutwardPoint c xi r ∉ closure Omega.carrier := by
  intro hout
  have hcint : c ∈ interior Omega.carrier := by
    rwa [Omega.isOpen_carrier.interior_eq]
  have hcombo :
      (1 - r) • c + r • smoothJordanOutwardPoint c xi r = xi := by
    unfold smoothJordanOutwardPoint
    rw [smul_add, smul_smul, mul_inv_cancel₀ hr.1.ne', one_smul]
    module
  have hxiint : xi ∈ interior Omega.carrier := by
    rw [← hcombo]
    exact
      Omega.strictConvex_carrier.convex.combo_interior_closure_mem_interior
        hcint hout (sub_pos.mpr hr.2) hr.1.le (by ring)
  have hxicarrier : xi ∈ Omega.carrier := by
    rwa [Omega.isOpen_carrier.interior_eq] at hxiint
  have hempty : xi ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hxicarrier, hxi⟩
  exact hempty
end SmoothJordanDomain
