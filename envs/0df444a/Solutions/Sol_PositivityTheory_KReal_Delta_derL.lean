-- Prove2me | solution 1 for PositivityTheory.KReal.Delta.derL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:51:21.623945+00:00
-- url     : https://prove2.me/submissions/ad3ccf1d-4ea5-41e6-ad21-339d402613a4

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
theorem _root_.solution (D : Derivation ℂ A A) (t : A ⊗[ℂ] B) (x : A) (y : B) :
    D.toLinearMap.rTensor B (t * (x ⊗ₜ[ℂ] y)) =
      D.toLinearMap.rTensor B t * (x ⊗ₜ[ℂ] y) + t * (D x ⊗ₜ[ℂ] y) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, Derivation.coeFn_coe,
      Derivation.leibniz, smul_eq_mul, TensorProduct.add_tmul]
    rw [add_comm, mul_comm x]
  | add a b ha hb => rw [add_mul, map_add, ha, hb, map_add, add_mul, add_mul]; abel
end PositivityTheory.KReal.Delta
