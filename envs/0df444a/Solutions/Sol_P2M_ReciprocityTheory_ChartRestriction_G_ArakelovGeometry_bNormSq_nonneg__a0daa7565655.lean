-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_bNormSq_nonneg__a0daa7565655
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:24:52.665876+00:00
-- url     : https://prove2.me/submissions/74945b66-6b58-4a5c-a49c-dae7ddd06c8d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC

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
theorem _root_.solution (μ : Measure (Ix κ → ℂ)) (m : ConeMetric ℂ (Ix κ)) {r n : ℕ}
    (s : Fin r → (Ix κ → ℂ) → ℂ) (c : Fin r → ℂ) : 0 ≤ bNormSq μ s (wgt m n) c := by
  unfold bNormSq
  refine MeasureTheory.integral_nonneg fun z => mul_nonneg (sq_nonneg _) ?_
  unfold wgt
  refine inv_nonneg.mpr ?_
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
