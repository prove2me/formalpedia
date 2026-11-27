-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eq_zero_of_sum_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:25:38.580498+00:00
-- url     : https://prove2.me/submissions/2657f150-d852-4c7d-8199-28f0a9844634

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adtEnum_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adtEnum_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mem_coordIdeal_of_isHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {y : Fin (D + 1) → Ω} (hy : coordIdeal ℤ y = ⊥) {N : ℕ}
    (u : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card → ℤ)
    (h : ∑ i, (u i : Ω) * ∏ t, y t ^ adtEnum D N i t = 0) : u = 0 := by
  classical
  set p : MvPolynomial (Fin (D + 1)) ℤ :=
    ∑ i, monomial (Finsupp.equivFunOnFinite.symm (adtEnum D N i)) (u i) with hp
  have hph : p.IsHomogeneous N := by
    refine IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_sum]
    have := Finset.Nat.mem_antidiagonalTuple.mp (adtEnum_mem D N i)
    simpa using this
  have hpa : aeval y p = 0 := by
    rw [hp, map_sum, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    simp [algebraMap_int_eq]
  have hp0 : p = 0 := by
    have := mem_coordIdeal_of_isHomogeneous (o := ℤ) (x := y) hph hpa
    rwa [hy, Ideal.mem_bot] at this
  funext i
  have hc := congrArg (coeff (Finsupp.equivFunOnFinite.symm (adtEnum D N i))) hp0
  rw [hp, coeff_sum, coeff_zero] at hc
  rw [Finset.sum_eq_single i (fun j _ hji => ?_) (by simp)] at hc
  · simpa using hc
  · rw [coeff_monomial, if_neg]
    intro hE
    exact hji (adtEnum_injective D N (by simpa using hE))
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
