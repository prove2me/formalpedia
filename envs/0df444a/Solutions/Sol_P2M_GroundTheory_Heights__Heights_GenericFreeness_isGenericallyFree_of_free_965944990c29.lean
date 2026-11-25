-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_free_965944990c29
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:36.140105+00:00
-- url     : https://prove2.me/submissions/0caf0035-e7bf-4105-a6e8-7b022f85f49c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc

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
open GroundTheory.Heights₂.Heights.GenericFreeness
open Module
universe u
variable {A : Type u} [CommRing A]
namespace GroundTheory.Heights₂.Heights.GenericFreeness
theorem _root_.solution [Nontrivial A] {M : Type*} [AddCommGroup M] [Module A M] [Module.Free A M] :
    IsGenericallyFree A M :=
  ⟨1, one_ne_zero, Module.free_of_isLocalizedModule (Submonoid.powers (1 : A))
    (LocalizedModule.mkLinearMap (Submonoid.powers (1 : A)) M)⟩
end GroundTheory.Heights₂.Heights.GenericFreeness
