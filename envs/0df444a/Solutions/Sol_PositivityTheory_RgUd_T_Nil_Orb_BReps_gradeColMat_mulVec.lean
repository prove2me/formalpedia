-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.gradeColMat_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:15.257804+00:00
-- url     : https://prove2.me/submissions/bca477b8-6c00-4438-991a-b708c453f06f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_GradeColMatMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Submodule
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
variable {k : Type} [Field k] {n : ℕ}
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution (b : Module.Basis (Fin n) k (Fin n → k)) (u : Fin n → k) :
    gradeColMat b *ᵥ u = ∑ i, u i • b i := by
  ext r
  simp [gradeColMat, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Finset.sum_apply, mul_comm]
end PositivityTheory.RgUd.T.Nil.Orb.BReps
