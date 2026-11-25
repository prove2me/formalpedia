-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_mat_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:25.710275+00:00
-- url     : https://prove2.me/submissions/fabfc3cb-b45b-4ad3-967a-94e003bcb4d3

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
theorem _root_.solution {ι : Type} (b : Module.Basis ι k (Fin n → k)) (X Y : Matrix (Fin n) (Fin n) k)
    (h : ∀ i, X *ᵥ b i = Y *ᵥ b i) : X = Y := by
  apply Matrix.toLin'.injective
  exact b.ext fun i => by simpa [Matrix.toLin'_apply] using h i
end PositivityTheory.RgUd.T.Nil.Orb.BReps
