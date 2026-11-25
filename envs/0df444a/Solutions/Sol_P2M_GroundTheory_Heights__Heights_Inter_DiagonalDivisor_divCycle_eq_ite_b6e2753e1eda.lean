-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalDivisor_divCycle_eq_ite_b6e2753e1eda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:33:37.920923+00:00
-- url     : https://prove2.me/submissions/d468ea61-8b3e-4c27-9988-e77486a8b367

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagDiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalDivisor_divCycle_of_mem_a95e3337f26a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalDivisor_divCycle_of_not_mem_a36e959a45bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_subsingleton_of_not_le_5e934b8b52e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_sup_span_mul_4461e376663a


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalDivisor
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalDivisor
theorem _root_.solution {P : Ideal (MRing ι)} [P.IsPrime] {s u : MRing ι} (hu : u ∉ P)
    (W : Ideal (MRing ι)) :
    divCycle P s W = if W ∈ divSupp P (s * u) then multAt (P ⊔ Ideal.span {s}) W else 0 := by
  by_cases hW : W ∈ divSupp P (s * u)
  · rw [if_pos hW]
    by_cases hWs : W ∈ divSupp P s
    · exact divCycle_of_mem hWs
    rw [divCycle_of_not_mem hWs]
    have hWp : W.IsPrime := hW.1.1.1
    by_cases hsW : s ∈ W
    · exfalso
      refine hWs ⟨⟨⟨hWp, sup_le (le_sup_left.trans hW.1.1.2)
        ((Ideal.span_singleton_le_iff_mem _).mpr hsW)⟩, fun Q hQ hQW => hW.1.2 ⟨hQ.1, ?_⟩ hQW⟩, hW.2⟩
      exact (sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self s))) P).trans hQ.2
    · have hnle : ¬ P ⊔ Ideal.span {s} ≤ W := fun h => hsW (h (Ideal.mem_sup_right (Ideal.subset_span rfl)))
      unfold multAt
      rw [dif_pos hWp, Module.length_eq_zero_iff.mpr
        (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W hnle)]
      rfl
  · rw [if_neg hW]
    refine divCycle_of_not_mem fun hWs => hW ⟨?_, hWs.2⟩
    exact NumbersDVR.mem_minimalPrimes_sup_span_mul hu hWs.1
end GroundTheory.Heights₂.Heights.Inter.DiagonalDivisor
