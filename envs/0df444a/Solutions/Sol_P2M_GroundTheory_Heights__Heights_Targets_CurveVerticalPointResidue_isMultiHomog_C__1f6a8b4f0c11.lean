-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_C__1f6a8b4f0c11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:09.372251+00:00
-- url     : https://prove2.me/submissions/6ab2664f-0fc5-4dc9-8c9b-88ef52b78c40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Inter.AvoidRing
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue
theorem _root_.solution (a : ℤ) : IsMultiHomog (C a : MRing ι) 0 := by
  classical
  intro m hm k
  have hm' : m ∈ (monomial (0 : (Σ k, ι k) →₀ ℕ) a).support := hm
  have := MvPolynomial.support_monomial_subset hm'
  rw [Finset.mem_singleton] at this
  subst this
  simp
end GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue
