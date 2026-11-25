-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesCoordDet_det_ne_zero_d33450b39a0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:00:59.11214+00:00
-- url     : https://prove2.me/submissions/eac58f77-d85a-4648-b879-bdc52234e5c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesCoordDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open GroundTheory.Heights₂.Heights.KLinesCoordDet
variable {K : Type} [Field K] {n m k : ℕ} (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K))
  (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)
namespace GroundTheory.Heights₂.Heights.KLinesCoordDet
theorem _root_.solution (hli : LinearIndependent K (Sum.elim b c)) :
    (B.toMatrix (Sum.elim b c)).det ≠ 0 := by
  have hcard : Fintype.card (Fin m ⊕ Fin k) = Module.finrank K (Fin n → K) :=
    (Module.finrank_eq_card_basis B).symm
  let v := basisOfLinearIndependentOfCardEqFinrank' (Sum.elim b c) hli hcard
  have hv : (v : Fin m ⊕ Fin k → Fin n → K) = Sum.elim b c :=
    coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have h := congrArg Matrix.det (Module.Basis.toMatrix_mul_toMatrix_flip B v)
  rw [det_mul, det_one, hv] at h
  exact left_ne_zero_of_mul_eq_one h
end GroundTheory.Heights₂.Heights.KLinesCoordDet
