-- Prove2me | solution 1 for P2M_GlobalTheory_isOpenImmersion_equalizer___left_of_unramified_3c023f0a11ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:34:08.004883+00:00
-- url     : https://prove2.me/submissions/09571449-6993-4d07-ba9b-67a8405e264d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian

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
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory
theorem _root_.solution {S : Scheme.{u}} {T X : Over S}
    [FormallyUnramified X.hom] [LocallyOfFiniteType X.hom] (a b : T ⟶ X) :
    IsOpenImmersion (equalizer.ι a b).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod a b).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
    (Over.prodLeftIsoPullback X X).hom]
  convert! (inferInstance : IsOpenImmersion (pullback.diagonal X.hom))
  ext1 <;> simp [← Over.comp_left]
end GlobalTheory
