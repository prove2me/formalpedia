-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalCardinality_holds_proof_f4dfbcbdf3d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:51.504695+00:00
-- url     : https://prove2.me/submissions/0ac350e4-8403-42a3-b9d1-c9806c0be570

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLength
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KrullDimQuotientEqOneIffEqBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_SpanSingletonEqRangeLsmul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_geoNum_zero_nonneg_bca26a562c32
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_span_singleton_eq_range_lsmul_f57f9a1eb403
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_card_eq_card_residueField_pow_length_9f7daccf84b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_locIdeal_eq_span_6d401f7ea2c7
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_krullDimLE_one_of_krullDim_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_coker_ne_top


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
namespace regularityLocalCardinality_holds
theorem _root_.solution (hD : regularityLocalDimension_holds.Statement) (hR : regularityLocalResidue_holds.Statement) : regularityLocalCardinality_holds.Statement := by
  intro K _ ι _ P s a W b y hP hs hsP hW hy hy0
  obtain ⟨hloc, hnoeth, hdim⟩ := hD K ι P s a W hP hs hsP hW
  have := hloc
  have := hnoeth
  have : P.IsPrime := hP.2.1.1
  have : IsDomain (locRing P W) := inferInstance
  have : Ring.KrullDimLE 1 (locRing P W) := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hdim
  obtain ⟨-, hcard⟩ := hR K ι P s a W b hP hs hsP hW
  have hy0' : (⟨y, hy⟩ : locRing P W) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have hfin : Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y) ≠ ⊤ := by
    rw [locIdeal_eq_span hy, span_singleton_eq_range_lsmul]
    exact ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top (locRing P W) hy0'
  rw [card_eq_card_residueField_pow_length _ hfin, hcard]
  have hg : (geoNum 0 W b : ℝ) = ((geoNum 0 W b).toNat : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (geoNum_zero_nonneg W b)).symm
  rw [hg]
  push_cast
  rw [Real.log_pow, Real.log_pow]
end regularityLocalCardinality_holds
end GroundTheory.Heights₂.Heights.Inter
