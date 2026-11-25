-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesCoordDet_toBlocks___eq_1b8652055f7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:01:03.420601+00:00
-- url     : https://prove2.me/submissions/fcc7450d-6b86-4840-9941-b4e60be77836

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
theorem _root_.solution (hb : ∀ i, B (Sum.inl i) = b i) :
    (B.toMatrix (Sum.elim b c)).toBlocks₂₁ = 0 := by
  ext i j
  rw [toBlocks₂₁, of_apply, Module.Basis.toMatrix_apply, Sum.elim_inl, ← hb, Module.Basis.repr_self,
    Finsupp.single_apply, Matrix.zero_apply, if_neg Sum.inl_ne_inr]
end GroundTheory.Heights₂.Heights.KLinesCoordDet
