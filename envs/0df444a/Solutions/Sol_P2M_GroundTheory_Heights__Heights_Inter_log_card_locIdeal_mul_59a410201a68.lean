-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_mul_59a410201a68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:49.665273+00:00
-- url     : https://prove2.me/submissions/9e85327e-d84e-4841-bd31-21302265f391

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_XcNotMemOfIsRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemFunFieldSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LogCardLocIdealUnitMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_card_quot_span_mul_90d58191fb18
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
theorem _root_.solution {P W : Ideal (MRing ι)} [P.IsPrime] {y₁ y₂ : FractionRing (MRing ι ⧸ P)}
    (h₁ : y₁ ∈ locRing P W) (h₂ : y₂ ∈ locRing P W) (hne : y₁ ≠ 0)
    (hf₁ : Finite (locRing P W ⧸ locIdeal P W y₁)) (hf₂ : Finite (locRing P W ⧸ locIdeal P W y₂)) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y₁ * y₂))) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W y₁)) + Real.log (Nat.card (locRing P W ⧸ locIdeal P W y₂)) := by
  rw [locIdeal_eq_span h₁] at hf₁ ⊢
  rw [locIdeal_eq_span h₂] at hf₂ ⊢
  rw [locIdeal_eq_span (mul_mem h₁ h₂)]
  have : (⟨y₁ * y₂, mul_mem h₁ h₂⟩ : locRing P W) = ⟨y₁, h₁⟩ * ⟨y₂, h₂⟩ := rfl
  rw [this, card_quot_span_mul _ _ (fun h => hne (congrArg Subtype.val h)), Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr Nat.card_pos.ne') (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]
end GroundTheory.Heights₂.Heights.Inter
