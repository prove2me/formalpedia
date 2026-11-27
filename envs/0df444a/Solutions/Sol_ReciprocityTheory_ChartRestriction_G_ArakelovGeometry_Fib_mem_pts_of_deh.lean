-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.mem_pts_of_deh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:25:24.846213+00:00
-- url     : https://prove2.me/submissions/f0d96c59-094f-4ded-956d-a43ea4264cde

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_aeval_eq_pow_mul_deh
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_coeff_coneMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] (x : ι → Ω) (z : ι → ℂ)
    (i₀ : ι) (hx : x i₀ ≠ 0) (hz : z i₀ ≠ 0)
    (h : ∀ G : MvPolynomial ι ℤ, deh x i₀ G = 0 → deh z i₀ G = 0) :
    z ∈ pts (coordIdeal ℤ x) := by
  refine ⟨fun h0 => hz (by rw [h0]; rfl), fun f hf => ?_⟩
  rw [coordIdeal, RingHom.mem_ker] at hf
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  have hd := homogeneousComponent_isHomogeneous d f
  have hx0 : aeval x (homogeneousComponent d f) = 0 := by
    rw [← coeff_coneMap, hf, Polynomial.coeff_zero]
  rw [aeval_eq_pow_mul_deh x i₀ hx hd] at hx0
  have hz0 := h _ ((mul_eq_zero.mp hx0).resolve_left (pow_ne_zero _ hx))
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def, aeval_eq_pow_mul_deh z i₀ hz hd, hz0, mul_zero]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
