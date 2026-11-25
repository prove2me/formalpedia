-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_unit_37194c2134d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:39.57486+00:00
-- url     : https://prove2.me/submissions/276ad4e5-e981-4ce3-a9d4-ccbf35eb4d13

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
theorem _root_.solution {P W : Ideal (MRing ι)} [P.IsPrime] {y z : FractionRing (MRing ι ⧸ P)}
    (hy : y ∈ locRing P W) (hz : z ∈ locRing P W) (h : y * z = 1) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W y)) = 0 := by
  rw [locIdeal_eq_span hy, Ideal.span_singleton_eq_top.mpr
    (IsUnit.of_mul_eq_one (⟨z, hz⟩ : locRing P W) (Subtype.ext h))]
  have : Subsingleton (locRing P W ⧸ (⊤ : Ideal (locRing P W))) := Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [Nat.card_of_subsingleton (0 : locRing P W ⧸ (⊤ : Ideal (locRing P W)))]
  simp
end GroundTheory.Heights₂.Heights.Inter
