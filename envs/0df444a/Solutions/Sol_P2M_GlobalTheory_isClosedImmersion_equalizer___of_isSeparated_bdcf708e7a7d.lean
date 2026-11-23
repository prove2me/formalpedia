-- Prove2me | solution 1 for P2M_GlobalTheory_isClosedImmersion_equalizer___of_isSeparated_bdcf708e7a7d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:46.316672+00:00
-- url     : https://prove2.me/submissions/2da41637-d8c0-4063-aa22-26bc9b1b8bca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_GlobalTheory_isPullback_equalizer_diagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X S T : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] {a b : T ⟶ X} (hab : a ≫ f = b ≫ f) :
    IsClosedImmersion (equalizer.ι a b) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_equalizer_diagonal f hab) inferInstance
end GlobalTheory
