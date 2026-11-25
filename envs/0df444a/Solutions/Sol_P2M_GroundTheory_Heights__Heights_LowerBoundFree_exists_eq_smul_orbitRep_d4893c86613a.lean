-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_eq_smul_orbitRep_d4893c86613a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:38.189798+00:00
-- url     : https://prove2.me/submissions/f66b2dfb-1de8-4c25-b9c7-31a8d4fed0bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution (z : (Σ k, ι k) → ℂ) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c (orbitRep z) :=
  Quotient.mk_out (s := torusSetoid (ι := ι)) z
end GroundTheory.Heights₂.Heights.LowerBoundFree
