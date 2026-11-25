-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_polyBasis_apply_ba9b92bb4178
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:57.169603+00:00
-- url     : https://prove2.me/submissions/dc9d2f83-691d-4139-b763-e96cc7c7b27a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) (i : ι) :
    polyBasis b n i = C (b i) := by
  simp [polyBasis, polyTensorEquiv, Algebra.TensorProduct.basis_apply, polyTensorAlgEquiv_tmul,
    smul_eq_C_mul]
end GroundTheory.Heights₂.Heights.Vertical
