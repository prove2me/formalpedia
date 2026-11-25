-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_max_mem_minimalPrimes_49103e6a00fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:18.445524+00:00
-- url     : https://prove2.me/submissions/bace8571-738b-443d-99c5-5937fa271bdc

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
omit [IsDomain A] [IsNoetherianRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading
theorem _root_.solution [IsLocalRing A] (h2 : ringKrullDim A = 2) (W : Ideal A) [hW : W.IsPrime]
    (h1 : W.height = 1) {b : A} (hbW : b ∉ W) (hbm : b ∈ maximalIdeal A) :
    maximalIdeal A ∈ (W ⊔ Ideal.span {b}).minimalPrimes := by
  have hle : W ⊔ Ideal.span {b} ≤ maximalIdeal A :=
    sup_le (le_maximalIdeal hW.ne_top) ((Ideal.span_singleton_le_iff_mem _).mpr hbm)
  refine ⟨⟨(maximalIdeal.isMaximal A).isPrime, hle⟩, fun Q hQ hQm => ?_⟩
  have := hQ.1
  by_contra hne
  have hlt : Q < maximalIdeal A := lt_of_le_of_ne hQm fun h => hne (h ▸ le_rfl)
  have hWQ : W < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h =>
    hbW (h ▸ hQ.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hWQ
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hm := maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [h2, show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at hm
  rw [WithBot.coe_injective hm] at e2
  rw [h1] at e1
  have : (1 : ℕ∞) + 1 + 1 ≤ 2 := le_trans (add_le_add e1 le_rfl) e2
  exact absurd this (by decide)
end GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading
