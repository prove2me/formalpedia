-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TildeFiniteE_proof_56edf186d493
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:54.420803+00:00
-- url     : https://prove2.me/submissions/2a1c9000-66c6-401d-94e7-bf8070557837

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteESt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFiniteE
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_toTildeH_surjective_da8a6cc05bed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_coneSubE_finite_60bbf6d09137


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace TildeFiniteE
theorem _root_.solution (h : SerreFinite.Statement.{u, v}) : TildeFiniteE.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M i c
  have : Module.Finite S (cohom M.coneGradedE i c) :=
    h S N M.coneSubE M.coneGradedE M.coneSubE_finite i c
  exact Module.Finite.of_surjective (toTildeH M c i) (toTildeH_surjective M c i)
end TildeFiniteE
end GroundTheory.Heights₂.Heights.Kleiman
