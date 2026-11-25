-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesCoordDet_det_eq_89a8912c4c84
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:42.058567+00:00
-- url     : https://prove2.me/submissions/c559549e-36b0-4c3f-82b9-3e0e59b0bb74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesCoordDet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesCoordDet_toBlocks___eq_e5da199bfdf2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesCoordDet_toBlocks___eq_1b8652055f7a

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
theorem _root_.solution (hb : ∀ i, B (Sum.inl i) = b i) :
    (B.toMatrix (Sum.elim b c)).det = (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det := by
  set P := B.toMatrix (Sum.elim b c) with hPdef
  have hP : P = fromBlocks 1 P.toBlocks₁₂ 0 P.toBlocks₂₂ := by
    rw [← toBlocks₁₁_eq B b c hb, ← toBlocks₂₁_eq B b c hb, fromBlocks_toBlocks]
  conv_lhs => rw [hP]
  rw [det_fromBlocks_zero₂₁, det_one, one_mul]
end GroundTheory.Heights₂.Heights.KLinesCoordDet
