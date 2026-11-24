-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.eq_bsmul_of_segre_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:30.257377+00:00
-- url     : https://prove2.me/submissions/eae9afd5-0af3-4028-9830-afbca239fe21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_prod_update_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {z z' : (Σ k, ι k) → ℂ} (i0 : (k : K) → ι k)
    (h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0) (hs : segre z = segre z') :
    (∀ k, z' ⟨k, i0 k⟩ ≠ 0) ∧ z' = bsmul (fun k => z' ⟨k, i0 k⟩ / z ⟨k, i0 k⟩) z := by
  classical
  have hseg : ∀ i : (k : K) → ι k, ∏ k, z ⟨k, i k⟩ = ∏ k, z' ⟨k, i k⟩ := fun i => congrFun hs i
  have hP0 : ∏ k, z ⟨k, i0 k⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => h0 k
  have h0' : ∀ k, z' ⟨k, i0 k⟩ ≠ 0 := by
    intro k
    have h1 : ∏ k, z' ⟨k, i0 k⟩ ≠ 0 := by rw [← hseg i0]; exact hP0
    exact Finset.prod_ne_zero_iff.1 h1 k (Finset.mem_univ _)
  refine ⟨h0', ?_⟩
  funext ⟨k, i⟩
  simp only [bsmul]
  have hA' : z ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ =
      z' ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ := by
    rw [← prod_update_eq z i0 k i, ← prod_update_eq z' i0 k i]
    exact hseg _
  have hB' : z ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z ⟨k', i0 k'⟩ =
      z' ⟨k, i0 k⟩ * ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ := by
    rw [← prod_update_eq z i0 k (i0 k), ← prod_update_eq z' i0 k (i0 k)]
    exact hseg _
  have hP' : ∏ k' ∈ Finset.univ.erase k, z' ⟨k', i0 k'⟩ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => h0' k'
  rw [div_mul_eq_mul_div, eq_div_iff (h0 k)]
  apply mul_right_cancel₀ hP'
  linear_combination (-(z ⟨k, i0 k⟩)) * hA' + z ⟨k, i⟩ * hB'
end ReciprocityTheory.ChartRestriction.G.Geo
