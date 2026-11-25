-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_quotient_bot_7804e84e449b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:08:18.599578+00:00
-- url     : https://prove2.me/submissions/46b097bb-1859-45a2-ac3e-b3467d198159

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFreeness
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreeness
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_linearEquiv_fa7014fc8534
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_isGenericallyFree_of_free_965944990c29


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
open MvPolynomial
universe u v w
open GroundTheory.Heights₂.Heights.GenericFreeness
namespace GroundTheory.Heights₂.Heights.GenericFreeness
theorem _root_.solution {A : Type u} [CommRing A] [IsDomain A] (σ : Type*) :
    IsGenericallyFree A (MvPolynomial σ A ⧸ (⊥ : Ideal (MvPolynomial σ A))) :=
  (isGenericallyFree_of_free (M := MvPolynomial σ A)).of_linearEquiv
    (AlgEquiv.quotientBot A (MvPolynomial σ A)).toLinearEquiv.symm
end GroundTheory.Heights₂.Heights.GenericFreeness
