-- Prove2me | solution 1 for P2M_GlobalTheory_isOpenImmersion_equalizer___of_unramified_d71f398b7582
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:45.320794+00:00
-- url     : https://prove2.me/submissions/0c9239c0-207e-4cd7-a076-bfc316b6cb50

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
    [FormallyUnramified f] [LocallyOfFiniteType f] {a b : T ⟶ X} (hab : a ≫ f = b ≫ f) :
    IsOpenImmersion (equalizer.ι a b) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_equalizer_diagonal f hab) inferInstance
end GlobalTheory
