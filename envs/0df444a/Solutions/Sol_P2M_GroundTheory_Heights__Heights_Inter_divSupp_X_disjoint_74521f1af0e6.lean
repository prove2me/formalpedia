-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_divSupp_X_disjoint_74521f1af0e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:58:52.596259+00:00
-- url     : https://prove2.me/submissions/73081943-cdbe-4e7d-befb-04c9c86e1335

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution :
    ∀ W, W ∈ divSupp (⊥ : Ideal (MRing (PBlk 2))) (Xc 2 0) → W ∉ divSupp ⊥ (Xc 2 1) := by
  intro W h0 h1
  have m0 : Xc 2 0 ∈ W := h0.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have m1 : Xc 2 1 ∈ W := h1.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  obtain ⟨i, hi⟩ := h0.2 ()
  fin_cases i
  exacts [hi m0, hi m1]
end GroundTheory.Heights₂.Heights.Inter
