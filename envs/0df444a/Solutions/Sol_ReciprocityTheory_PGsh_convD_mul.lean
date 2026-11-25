-- Prove2me | solution 1 for ReciprocityTheory.PGsh.convD_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:40:48.923807+00:00
-- url     : https://prove2.me/submissions/d655ad67-704a-4f21-a4fc-f65f8f75c44b

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial TensorProduct
namespace ReciprocityTheory.PGsh
section Bialg
variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
private lemma rid_convolution_derivation (δ : A →ₗ[R] R) (hδ : IsPtDer δ) (u v : A ⊗[R] A) :
    (TensorProduct.rid R A) (δ.lTensor A (u * v)) =
      (TensorProduct.rid R A) ((Coalgebra.counit (R := R) (A := A)).lTensor A u) *
          (TensorProduct.rid R A) (δ.lTensor A v) +
        (TensorProduct.rid R A) (δ.lTensor A u) *
          (TensorProduct.rid R A) ((Coalgebra.counit (R := R) (A := A)).lTensor A v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u u' hu hu' => simp only [add_mul, map_add, hu, hu']; ring
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v v' hv hv' => simp only [mul_add, map_add, hv, hv']; ring
    | tmul c e =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, hδ b e, Algebra.smul_def, map_add, map_mul]
      ring
end Bialg
section Chain
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
end Chain
section Coeff
variable {R : Type*} [CommRing R] {d p : ℕ}
end Coeff
section Bialg2
variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
end Bialg2
section Core
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {d p : ℕ}
end Core
end ReciprocityTheory.PGsh
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (δ : A →ₗ[R] R) (hδ : IsPtDer δ) (f g : A) :
    convD δ (f * g) = f * convD δ g + g * convD δ f := by
  have hE : ∀ a : A, (TensorProduct.rid R A)
      ((Coalgebra.counit (R := R) (A := A)).lTensor A (Coalgebra.comul a)) = a := by
    intro a; rw [Coalgebra.lTensor_counit_comul]; simp
  simp only [convD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Bialgebra.comul_mul]
  rw [rid_convolution_derivation δ hδ, hE, hE]; ring
end ReciprocityTheory.PGsh
