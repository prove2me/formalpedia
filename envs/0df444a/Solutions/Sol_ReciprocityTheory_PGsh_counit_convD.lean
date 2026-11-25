-- Prove2me | solution 1 for ReciprocityTheory.PGsh.counit_convD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:40:53.403698+00:00
-- url     : https://prove2.me/submissions/34adfd63-7b52-42ea-aba6-dedff400e209

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (δ : A →ₗ[R] R) (f : A) :
    Coalgebra.counit (R := R) (convD δ f) = δ f := by
  have key : ∀ u : A ⊗[R] A, Coalgebra.counit (R := R) ((TensorProduct.rid R A) (δ.lTensor A u)) =
      δ ((TensorProduct.lid R A) ((Coalgebra.counit (R := R) (A := A)).rTensor A u)) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul a b => simp [mul_comm]
  simp only [convD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, key,
    Coalgebra.rTensor_counit_comul]
  simp
end ReciprocityTheory.PGsh
