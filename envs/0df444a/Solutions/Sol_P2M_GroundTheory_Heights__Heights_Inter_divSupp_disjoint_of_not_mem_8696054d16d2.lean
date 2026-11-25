-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_divSupp_disjoint_of_not_mem_8696054d16d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:58:54.039867+00:00
-- url     : https://prove2.me/submissions/0cce8110-a31d-49aa-87fd-071ea12e2b3a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PWellDefined

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
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {u a : MRing ι} (h : ∀ W ∈ divSupp P u, a ∉ W) :
    ∀ W, W ∈ divSupp P u → W ∉ divSupp P a :=
  fun W hW hW' => h W hW (hW'.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
end GroundTheory.Heights₂.Heights.Inter
