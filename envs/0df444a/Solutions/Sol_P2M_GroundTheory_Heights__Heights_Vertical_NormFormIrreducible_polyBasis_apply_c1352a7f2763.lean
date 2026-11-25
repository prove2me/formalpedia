-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormIrreducible_polyBasis_apply_c1352a7f2763
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:23:28.450644+00:00
-- url     : https://prove2.me/submissions/2e895a20-372f-41e3-aa34-771ea26ddd00

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormIrreducible

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
open MvPolynomial TensorProduct Matrix
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
open GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
theorem _root_.solution {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) (i : ι) :
    polyBasis b n i = C (b i) := by
  simp [polyBasis, polyTensorEquiv, Algebra.TensorProduct.basis_apply, polyTensorAlgEquiv_tmul,
    smul_eq_C_mul]
end GroundTheory.Heights₂.Heights.Vertical.NormFormIrreducible
