-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_divCycle_apply_of_not_mem_bf629faf9af2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:58:51.38433+00:00
-- url     : https://prove2.me/submissions/0c89b484-b570-4588-85b3-3f96b512c223

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {P W : Ideal (MRing ι)} {s : MRing ι} (h : W ∉ divSupp P s) :
    divCycle P s W = 0 := by
  classical
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  rw [if_neg h]
end GroundTheory.Heights₂.Heights.Inter
