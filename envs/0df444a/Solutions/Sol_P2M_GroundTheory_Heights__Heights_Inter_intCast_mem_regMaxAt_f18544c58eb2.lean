-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_intCast_mem_regMaxAt_f18544c58eb2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:11:44.034162+00:00
-- url     : https://prove2.me/submissions/00f7e5fc-b261-4da6-8b4d-cce31da7f62a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IntCastMemRegMaxAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_not_mem_regMaxAt_iff_e86bcbf427f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isMultiHomog_C_8aa21e557757
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_one_6a94195931fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityDenominator_isMultiHomog_C_6474a899c711
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isMultiHomog_one


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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (hL : LocRingLocal.Statement) {P W : Ideal (MRing ι)} (hPp : P.IsPrime)
    (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) {n : ℤ} (hn : C n ∈ W) :
    (n : regRing P) ∈ regMaxAt P W hW hPW hloc := by
  by_contra h
  obtain ⟨z, hz, h⟩ := (not_mem_regMaxAt_iff hW hPW hloc _).1 h
  have h1W : (1 : MRing ι) ∉ W := fun h => hW.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hu := ((hL K ι P W hPp hW.1.1 hPW).2 (n : locRing P W) (C n) 1 0 (RegularityDenominator.isMultiHomog_C n)
    AvoidRing.isMultiHomog_one h1W (by simp [eq_intCast C n])).1
  refine hu (IsUnit.of_mul_eq_one (a := (n : locRing P W)) ⟨z, hz⟩ (Subtype.ext ?_)) hn
  simpa using h
end GroundTheory.Heights₂.Heights.Inter
