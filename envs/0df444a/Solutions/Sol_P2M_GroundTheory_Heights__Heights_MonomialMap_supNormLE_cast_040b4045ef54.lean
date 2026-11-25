-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_cast_040b4045ef54
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:28:35.00216+00:00
-- url     : https://prove2.me/submissions/7083b188-a9dd-4b0a-98b2-eb99e09d411b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroAlt

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
noncomputable section
open GroundTheory.Heights₂.Heights.MonomialMap
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n}
namespace GroundTheory.Heights₂.Heights.MonomialMap
theorem _root_.solution (A B : HermLine n) (hdeg : A.deg = B.deg) (hmet : ∀ z, A.metric z = B.metric z)
    (s : IntegralSection P A.deg) {C : ℝ} (hs : s.SupNormLE A C) :
    (s.cast hdeg).SupNormLE B C := by
  intro z hz c d e he hc
  have he' : IsChartForm P A.deg s.num s.den c d e := by
    obtain ⟨⟨δ, hδ, hδk⟩, hmem⟩ := he
    exact ⟨⟨δ, hδ, fun k ↦ by rw [hδk k, hdeg]⟩, hmem⟩
  rw [← hmet z]
  exact hs z hz c d e he' hc
end GroundTheory.Heights₂.Heights.MonomialMap
