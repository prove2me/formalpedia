-- Prove2me | solution 1 for P2M_GlobalTheory_MaxIdealJointEigen_mulVec_eval__627d53cb6c27
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:09:37.695951+00:00
-- url     : https://prove2.me/submissions/5585b0cb-0ffc-4b59-9483-7ab53f7fc43a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfIntegralMatrixUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalIdealEqJointEigen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory GlobalTheory.MaxIdealJointEigen
namespace GlobalTheory.MaxIdealJointEigen
theorem _root_.solution {O K I : Type} [CommRing O] [Field K] (emb : O →+* K) {n : ℕ}
    (ρ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O) (θ : I → K) (c : Fin n → K)
    (hc : ∀ i, ((ρ (X i)).map emb).mulVec c = θ i • c) (p : MvPolynomial I O) :
    ((ρ p).map emb).mulVec c = eval₂ emb θ p • c := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Matrix.algebraMap_eq_diagonal]
    ext j
    simp [Matrix.mulVec_diagonal]
  | add p q hp hq =>
    rw [map_add, Matrix.map_add _ (map_add emb), Matrix.add_mulVec, hp, hq, eval₂_add, add_smul]
  | mul_X p i hp =>
    rw [map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hp, eval₂_mul,
      eval₂_X, smul_smul, mul_comm]
end GlobalTheory.MaxIdealJointEigen
