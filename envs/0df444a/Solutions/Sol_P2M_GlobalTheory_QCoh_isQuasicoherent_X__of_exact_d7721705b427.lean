-- Prove2me | solution 1 for P2M_GlobalTheory_QCoh_isQuasicoherent_X__of_exact_d7721705b427
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:51:23.421074+00:00
-- url     : https://prove2.me/submissions/b41400ae-682a-4b4e-a7b6-e7b98d9e57c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe w' w u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {M N P : X.Modules} {U V : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution {S : ShortComplex X.Modules} (hS : S.Exact) [Epi S.g]
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] : S.X₃.IsQuasicoherent :=
  isQuasicoherent_of_isColimit hS.gIsCokernel
end GlobalTheory.QCoh
