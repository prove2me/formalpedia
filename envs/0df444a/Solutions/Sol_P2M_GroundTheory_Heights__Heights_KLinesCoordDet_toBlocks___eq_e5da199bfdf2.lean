-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesCoordDet_toBlocks___eq_e5da199bfdf2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:01:04.98607+00:00
-- url     : https://prove2.me/submissions/0569a3e4-000c-4a99-96e6-04f3bd70f316

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
    (B.toMatrix (Sum.elim b c)).toBlocks₁₁ = 1 := by
  ext i j
  rw [toBlocks₁₁, of_apply, Module.Basis.toMatrix_apply, Sum.elim_inl, ← hb, Module.Basis.repr_self,
    Finsupp.single_apply, one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (fun e => h (Sum.inl_injective e).symm), if_neg h]
end GroundTheory.Heights₂.Heights.KLinesCoordDet
