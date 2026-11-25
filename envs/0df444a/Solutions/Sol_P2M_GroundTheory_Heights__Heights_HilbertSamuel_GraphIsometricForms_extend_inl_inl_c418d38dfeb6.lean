-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometricForms_extend_inl_inl_c418d38dfeb6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:55:43.838861+00:00
-- url     : https://prove2.me/submissions/2a3b248a-543e-4028-8aa1-feebd81006db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
variable {K K₂ M : Type*} [Zero M]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
theorem _root_.solution (f : K → M) (k : K) : Function.extend (Sum.inl : K → K ⊕ K₂) f 0 (Sum.inl k) = f k :=
  Sum.inl_injective.extend_apply _ _ _
end GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms
