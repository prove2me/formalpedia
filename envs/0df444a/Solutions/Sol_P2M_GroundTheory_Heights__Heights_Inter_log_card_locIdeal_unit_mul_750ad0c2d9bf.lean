-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_unit_mul_750ad0c2d9bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:26:35.167797+00:00
-- url     : https://prove2.me/submissions/a59f61b3-02e9-4f0d-baa6-4709c4737088

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_XcNotMemOfIsRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemFunFieldSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LogCardLocIdealUnitMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_locIdeal_eq_span_6d401f7ea2c7


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
theorem _root_.solution {P W : Ideal (MRing ι)} [P.IsPrime] {y z c : FractionRing (MRing ι ⧸ P)}
    (hy : y ∈ locRing P W) (hz : z ∈ locRing P W) (h : y * z = 1) (hc : c ∈ locRing P W) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y * c))) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W c)) := by
  rw [locIdeal_eq_span (mul_mem hy hc), locIdeal_eq_span hc]
  have : (⟨y * c, mul_mem hy hc⟩ : locRing P W) = ⟨y, hy⟩ * ⟨c, hc⟩ := rfl
  rw [this, Ideal.span_singleton_mul_left_unit (IsUnit.of_mul_eq_one (⟨z, hz⟩ : locRing P W) (Subtype.ext h))]
end GroundTheory.Heights₂.Heights.Inter
