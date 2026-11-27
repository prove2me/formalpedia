-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_proof_aabab4a27e73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:17.997735+00:00
-- url     : https://prove2.me/submissions/13beaa41-5d67-44b5-a100-32c4db9995a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyGermPointPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolyGermPointPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_pointIdeal_pow_le_9b912c280ece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_mem_pow_ker_of_isBigO_5ce8b9ce1fd7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter Asymptotics
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PolyGermPointPow
theorem _root_.solution : PolyGermPointPow.Statement := by
  intro σ _ w k q hq
  obtain ⟨f, hf, hfO⟩ := PolyGermPointPow.pointIdeal_pow_le w k hq
  have hf' : (f : Germ (𝓝 w) ℂ) = ((fun z => eval z q : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := hf
  exact PolyGermPointPow.mem_pow_ker_of_isBigO w (hfO.congr' (Germ.coe_eq.mp hf') EventuallyEq.rfl)
end PolyGermPointPow
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
