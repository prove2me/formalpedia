-- Prove2me | solution 1 for P2M_GlobalTheory_QCoh_isQuasicoherent_X__of_exact_0f6dd0a142c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:57:15.686844+00:00
-- url     : https://prove2.me/submissions/b45acc2f-04a2-4c99-aa2f-2f1dbc219f49

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
theorem _root_.solution {S : ShortComplex X.Modules} (hS : S.Exact) [Mono S.f]
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] : S.X₁.IsQuasicoherent :=
  isQuasicoherent_of_exact_app S.f S.g (fun U _ ↦ injective_app_of_mono S.f U)
    fun U _ ↦ exact_app_of_exact_of_mono hS U
end GlobalTheory.QCoh
