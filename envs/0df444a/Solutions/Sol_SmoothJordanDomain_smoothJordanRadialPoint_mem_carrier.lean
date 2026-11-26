-- Prove2me | solution 1 for SmoothJordanDomain.smoothJordanRadialPoint_mem_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:14:28.539261+00:00
-- url     : https://prove2.me/submissions/58b5b64c-8971-44db-bdd7-6a41ed6955ac

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
    (Omega : SmoothJordanDomain) {c z : ℂ}
    (hc : c ∈ Omega.carrier) (hz : z ∈ closure Omega.carrier)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    smoothJordanRadialPoint c z r ∈ Omega.carrier := by
  have hcint : c ∈ interior Omega.carrier := by
    rwa [Omega.isOpen_carrier.interior_eq]
  have hmem : smoothJordanRadialPoint c z r ∈ interior Omega.carrier := by
    unfold smoothJordanRadialPoint
    exact
      Omega.strictConvex_carrier.convex.combo_interior_closure_mem_interior
        hcint hz (sub_pos.mpr hr.2) hr.1.le (by ring)
  exact interior_subset hmem
end SmoothJordanDomain
