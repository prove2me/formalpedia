-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.neg_log_det_monoDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:26:10.66171+00:00
-- url     : https://prove2.me/submissions/8de125fd-80b4-4e67-a1d6-e9417f18aa34

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CNormSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_HadZSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sum_adtEnum
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
open scoped ComplexOrder
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (D N δ : ℕ) :
    -(1 / 2) * Real.log (monoDiag D N δ).det.re = δ * chiP D N := by
  have hpos : ∀ a : Fin (D + 1) → ℕ, 0 < monoNormSq a := fun a => by
    unfold monoNormSq
    positivity
  have hdet : (monoDiag D N δ).det.re =
      ∏ p : Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card),
        monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2) := by
    rw [monoDiag, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]
  rw [hdet, Real.log_prod fun p _ => (hpos _).ne']
  rw [← finProdFinEquiv.sum_comp (fun p => Real.log (monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2)))]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_adtEnum D N (fun a => Real.log (monoNormSq a)), chiP]
  ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
