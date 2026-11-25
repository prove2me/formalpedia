-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TildeVanish_proof_a4cf1446a4a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:06.764449+00:00
-- url     : https://prove2.me/submissions/c9429390-ea63-4f86-afa2-ee92dc72c88f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tildeSys_H_subsingleton_6de3c2c225fd
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
namespace TildeVanish
theorem _root_.solution (h : SerreVanish.Statement.{u, v}) : TildeVanish.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M
  obtain ⟨c₀, hc₀⟩ := h S N M.coneSubE M.coneGradedE M.coneSubE_finite
  refine ⟨c₀, fun i hi c hc => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  exact tildeSys_H_subsingleton M c k (hc₀ (k + 1) hi c hc)
end TildeVanish
end GroundTheory.Heights₂.Heights.Kleiman
