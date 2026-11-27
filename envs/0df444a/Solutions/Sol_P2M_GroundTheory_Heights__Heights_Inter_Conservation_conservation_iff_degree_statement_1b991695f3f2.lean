-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_Conservation_conservation_iff_degree_statement_1b991695f3f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:01:17.566677+00:00
-- url     : https://prove2.me/submissions/0ca43002-ac25-4c7c-b47e-08c1936eecaf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
namespace GroundTheory.Heights₂.Heights.Inter
namespace Conservation
theorem _root_.solution :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Conservation.Statement ↔ DegreeStatement := by
  constructor
  · intro h K _ ι _ P e L p hP hL hp
    rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)]
    exact (h K ι P e L p hP hL hp).symm
  · intro h K _ ι _ P e L p hP hL hp
    have h' := h K ι P e L p hP hL hp
    rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)] at h'
    exact h'.symm
end Conservation
end GroundTheory.Heights₂.Heights.Inter
