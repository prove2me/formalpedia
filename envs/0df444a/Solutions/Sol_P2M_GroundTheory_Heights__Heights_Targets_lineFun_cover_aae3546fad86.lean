-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_lineFun_cover_aae3546fad86
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:29.096106+00:00
-- url     : https://prove2.me/submissions/0761d22c-25c2-40b2-8112-48edc9a847db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsDivPushMultComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeBranchLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution (v : (Σ k : Unit, PBlk 2 k) → ℂ) (hv : v ∈ Metric.ball ptZeroOne (1 / 2)) :
    ∃ t ∈ Metric.ball (0 : Fin 2 → ℂ) (1 / 2), lineFun t = v ∧ t 0 = v ⟨(), 0⟩ := by
  rw [Metric.mem_ball, dist_pi_lt_iff (by norm_num)] at hv
  have h0 := hv ⟨(), 0⟩
  have h1 := hv ⟨(), 1⟩
  simp only [ptZeroOne, dist_eq_norm] at h0 h1
  refine ⟨![v ⟨(), 0⟩, v ⟨(), 1⟩ - 1], ?_, ?_, rfl⟩
  · rw [mem_ball_zero_iff, pi_norm_lt_iff (by norm_num)]
    intro i
    fin_cases i
    · simpa using h0
    · simpa using h1
  · funext q
    obtain ⟨⟨⟩, i⟩ := q
    fin_cases i <;> simp [lineFun]
end GroundTheory.Heights₂.Heights.Targets
