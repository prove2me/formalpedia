-- Prove2me | solution 1 for SmoothJordanDomain.canonicalNormal_support_all_of_support_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:44:19.239823+00:00
-- url     : https://prove2.me/submissions/14582585-fd8b-4139-abbd-6ae3763bbcc8

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Theorems.Thm_SmoothJordanDomain_closure_support_and_carrier_strict_of_support_at_mem_carrier

set_option autoImplicit false
open Complex Set
open scoped Real
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (t0 : ℝ)
    (hcside :
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t0) *
        (c - Omega.boundaryParam t0)).re ≤ 0) :
    ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0 := by
  let f : ℝ → ℝ := fun t ↦
    ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
      (c - Omega.boundaryParam t)).re
  have hgamma : Continuous Omega.boundaryParam :=
    Omega.boundaryParam_contDiff.continuous
  have hderiv : Continuous (deriv Omega.boundaryParam) :=
    Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)
  have hfcont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hfne : ∀ t, f t ≠ 0 := by
    intro t hzero
    have hstrict :=
      (Omega.closure_support_and_carrier_strict_of_support_at_mem_carrier
        c hc t (by
          change f t ≤ 0
          exact hzero.le)).2 c hc
    change f t < 0 at hstrict
    exact (ne_of_lt hstrict) hzero
  have hfneg : f t0 < 0 := by
    have hstrict :=
      (Omega.closure_support_and_carrier_strict_of_support_at_mem_carrier
        c hc t0 hcside).2 c hc
    exact hstrict
  intro t
  change f t ≤ 0
  by_contra ht
  have htpos : 0 < f t := lt_of_not_ge ht
  have hzeroMem : 0 ∈ Set.range f :=
    (intermediate_value_univ t0 t hfcont) ⟨hfneg.le, htpos.le⟩
  obtain ⟨u, hu⟩ := hzeroMem
  exact hfne u hu
end SmoothJordanDomain
