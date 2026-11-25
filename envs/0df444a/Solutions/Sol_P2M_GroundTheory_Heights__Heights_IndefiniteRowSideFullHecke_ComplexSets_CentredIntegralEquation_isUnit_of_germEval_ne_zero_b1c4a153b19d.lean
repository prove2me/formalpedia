-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_isUnit_of_germEval_ne_zero_b1c4a153b19d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:31:25.826361+00:00
-- url     : https://prove2.me/submissions/66540f18-f614-4dff-a688-bfeb14c9ca92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermPrimitivePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermCentredIntegralEquation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CentredIntegralEquation_germEval_toGerm_44cc721d23db

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
open Topology Filter Polynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation
open PrimeGermPrimitivePresentation
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation
theorem _root_.solution {w : σ → ℂ} (s : holGerms w) (hs : germEval w s ≠ 0) : IsUnit s := by
  obtain ⟨u, rfl⟩ := toGerm_surjective w s
  rw [germEval_toGerm] at hs
  have hu : AnalyticAt ℂ u.1 w := u.2
  refine IsUnit.of_mul_eq_one (toGerm w ⟨fun z => (u.1 z)⁻¹, hu.inv hs⟩) ?_
  rw [← map_mul, ← map_one (toGerm w)]
  apply Subtype.ext
  refine Germ.coe_eq.2 ((hu.continuousAt.eventually_ne hs).mono fun z hz => ?_)
  exact mul_inv_cancel₀ hz
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CentredIntegralEquation
