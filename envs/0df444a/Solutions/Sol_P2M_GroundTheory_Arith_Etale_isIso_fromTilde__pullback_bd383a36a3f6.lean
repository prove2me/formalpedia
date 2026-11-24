-- Prove2me | solution 1 for P2M_GroundTheory_Arith_Etale_isIso_fromTilde__pullback_bd383a36a3f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:33:51.133831+00:00
-- url     : https://prove2.me/submissions/48e1f4f7-1372-49c2-98f4-ceeca6715a77

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
namespace GroundTheory.Arith.Etale
theorem _root_.solution {A R : CommRingCat.{u}} (φ : A ⟶ R) (N : (Spec A).Modules)
    [IsIso N.fromTildeΓ] :
    IsIso ((Scheme.Modules.pullback (Spec.map φ)).obj N).fromTildeΓ := by
  rw [isIso_fromTildeΓ_iff]
  exact ⟨_, ⟨((pullbackTildeIso φ).app _).symm ≪≫
    (Scheme.Modules.pullback (Spec.map φ)).mapIso (@asIso _ _ _ _ N.fromTildeΓ ‹_›)⟩⟩
end GroundTheory.Arith.Etale
