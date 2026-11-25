-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.norm_monoC_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:59:13.505612+00:00
-- url     : https://prove2.me/submissions/1e6e80a9-7d38-4b09-b43c-6cb5a62d49f5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {N : ℕ} (a : Fin N → ℕ) (w : Fin N → ℂ) :
    ‖monoC a w‖ ^ 2 ≤ sqN w ^ (∑ i, a i) := by
  rw [monoC, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
  rw [norm_pow, ← pow_mul, mul_comm, pow_mul]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  exact Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
