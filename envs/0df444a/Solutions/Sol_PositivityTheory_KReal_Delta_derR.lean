-- Prove2me | solution 1 for PositivityTheory.KReal.Delta.derR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:32.568515+00:00
-- url     : https://prove2.me/submissions/4fa32c44-f724-4c49-83d9-1e6f9e239df2

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace TensorProduct
open PositivityTheory PositivityTheory.KReal
open PositivityTheory.KReal.Delta
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
namespace PositivityTheory.KReal.Delta
theorem _root_.solution (D : Derivation ℂ B B) (t : A ⊗[ℂ] B) (x : A) (y : B) :
    D.toLinearMap.lTensor A (t * (x ⊗ₜ[ℂ] y)) =
      D.toLinearMap.lTensor A t * (x ⊗ₜ[ℂ] y) + t * (x ⊗ₜ[ℂ] D y) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, Derivation.coeFn_coe,
      Derivation.leibniz, smul_eq_mul, TensorProduct.tmul_add]
    rw [add_comm, mul_comm y]
  | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, add_mul, add_mul]; abel
end PositivityTheory.KReal.Delta
