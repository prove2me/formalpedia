-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_mem_minimalPrimes_iff_4ff3b0367414
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:20.147724+00:00
-- url     : https://prove2.me/submissions/4ec9eae0-baff-4b96-993f-883e24d0033c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimTwoSumReading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading
variable {A : Type*} [CommRing A]
variable [IsDomain A] [IsNoetherianRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading
theorem _root_.solution {a : A} (ha : a ≠ 0) (W : Ideal A) [W.IsPrime] :
    W ∈ (Ideal.span {a}).minimalPrimes ↔ W.height = 1 ∧ a ∈ W := by
  have : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  constructor
  · intro hW
    have haW : a ∈ W := hW.1.2 (Ideal.subset_span rfl)
    have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) W hW
    have h0 : W.height ≠ 0 := fun h => ha ((Ideal.mem_bot).mp (Ideal.height_eq_zero_iff_eq_bot.mp h ▸ haW))
    exact ⟨le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h0), haW⟩
  · rintro ⟨h1, haW⟩
    obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {a}) (J := W)
      ((Ideal.span_singleton_le_iff_mem W).mpr haW)
    rcases hQW.lt_or_eq with hlt | rfl
    · have := hQ.1.1
      have haQ : a ∈ Q := hQ.1.2 (Ideal.subset_span rfl)
      have hbQ : ⊥ < Q := bot_lt_iff_ne_bot.mpr fun h => ha ((Ideal.mem_bot).mp (h ▸ haQ))
      have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hbQ
      have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [Ideal.height_bot, zero_add] at e1
      rw [h1] at e2
      have : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add e1 le_rfl) e2
      exact absurd this (by decide)
    · exact hQ
end GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading
