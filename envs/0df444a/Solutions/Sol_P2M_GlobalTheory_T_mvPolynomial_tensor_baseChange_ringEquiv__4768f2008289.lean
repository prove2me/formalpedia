-- Prove2me | solution 1 for P2M_GlobalTheory_T_mvPolynomial_tensor_baseChange_ringEquiv__4768f2008289
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:53:29.13234+00:00
-- url     : https://prove2.me/submissions/f30f327d-1e93-4051-a039-1c9e0becec3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialTensorBaseChangeRingEquiv
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialTensorBaseChangeRingEquivStatement
import Theorems.Thm_GlobalTheory_mvPolynomial_tensor_baseChange_ringEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S B K τ : Type) [CommRing S] [CommRing B] [CommRing K] [Algebra S B] [Algebra S K] [Algebra (MvPolynomial τ S) K] [IsScalarTower S (MvPolynomial τ S) K], letI : Algebra (MvPolynomial τ S) (MvPolynomial τ B) := (MvPolynomial.map (algebraMap S B)).toAlgebra; Nonempty (MvPolynomial τ B ⊗[MvPolynomial τ S] K ≃+* B ⊗[S] K) := by
  first | exact @GlobalTheory.mvPolynomial_tensor_baseChange_ringEquiv | exact GlobalTheory.mvPolynomial_tensor_baseChange_ringEquiv | (intros; apply GlobalTheory.mvPolynomial_tensor_baseChange_ringEquiv <;> assumption)
end _root_.GlobalTheory.T
