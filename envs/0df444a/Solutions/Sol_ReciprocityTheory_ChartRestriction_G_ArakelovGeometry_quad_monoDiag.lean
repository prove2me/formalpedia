-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.quad_monoDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:37:18.725352+00:00
-- url     : https://prove2.me/submissions/f5774541-e307-450f-844f-2e3ca3af3d42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
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
open Matrix
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (D N δ : ℕ) (v : Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card) → ℂ) :
    (star v ⬝ᵥ monoDiag D N δ *ᵥ v).re =
      ∑ l : Fin δ, ∑ i, monoNormSq (adtEnum D N i) * ‖v (finProdFinEquiv (l, i))‖ ^ 2 := by
  simp only [monoDiag, Matrix.mulVec_diagonal]
  first
  | simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]
  | simp only [Matrix.dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]
  rw [Complex.re_sum, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  try simp only [Equiv.symm_apply_apply]
  rw [mul_left_comm, Complex.re_ofReal_mul]
  congr 1
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
