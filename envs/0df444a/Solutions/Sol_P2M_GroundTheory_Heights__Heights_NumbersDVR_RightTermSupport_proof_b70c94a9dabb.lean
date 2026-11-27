-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_RightTermSupport_proof_b70c94a9dabb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:05:27.778423+00:00
-- url     : https://prove2.me/submissions/7a743b81-90ee-4090-bbd8-41cf68c03f53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PColonMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsSide
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IsMultiHomogIdeal_sup_4e558288843a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ColonMultiHomog_proof_89514dc80a8c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialQuotDim_proof_5536281ab8d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SupSpanMultiHomog_proof_861d53cbe2c3


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
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace RightTermSupport
theorem _root_.solution : RightTermSupport.Statement.{u} := by
  intro O _ _ _ ϖ K _ _ ι _ P hP b f g hD c s hs hH W U hU
  by_contra hne
  have hW : divCycle P s W ≠ 0 := left_ne_zero_of_mul hne
  have hWU : idealCycle (W ⊔ divisorIdeal P f g) U ≠ 0 := right_ne_zero_of_mul hne
  have hWm : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h
    · exact absurd rfl hW
  have hUm : U ∈ (W ⊔ divisorIdeal P f g).minimalPrimes ∧ IsRelevant U := by
    unfold idealCycle at hWU
    split_ifs at hWU with h
    · exact h
    · exact absurd rfl hWU
  have hWp : W.IsPrime := hWm.1.1.1
  have hUp : U.IsPrime := hUm.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hWm.1.1.2
  have hWU' : W ≤ U := le_sup_left.trans hUm.1.1.2
  have hDU : divisorIdeal P f g ≤ U := le_sup_right.trans hUm.1.1.2
  have hWmh : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.proof O K ι _ W (SupSpanMultiHomog.proof O K ι P s c hP hs) hWm.1
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.1.degrees
  have hDm : IsMultiHomogIdeal (divisorIdeal P f g) :=
    ColonMultiHomog.proof O K ι _ g bg (SupSpanMultiHomog.proof O K ι P f bf hP hbf) hbg
  have hUmh : IsMultiHomogIdeal U :=
    MinimalPrimeMultiHomog.proof O K ι _ U (hWmh.sup hDm) hUm.1
  apply hU
  refine ⟨hUp, hUmh, hUm.2, ?_, hPW.trans hWU'⟩
  by_cases hϖW : (C ϖ : MRing ι O) ∈ W
  · exact hWU' hϖW
  by_contra hϖU
  have hV := hH W hW hϖW
  obtain ⟨u, v, hu, hv, huv⟩ := hV.unit_off_special U hUp hWU' hUm.2 hϖU
  obtain ⟨u', v', hu', huv'⟩ := hD.2 U hUp (hPW.trans hWU') hUm.2
  have hv'D : v' ∈ divisorIdeal P f g := by
    unfold divisorIdeal
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    have e : v' * g = u' * f - (u' * f - v' * g) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
      (Ideal.mem_sup_left huv')
  have hmem : g * (u * v' - u' * v) ∈ W := by
    have e : g * (u * v' - u' * v) = u' * (u * f - v * g) - u * (u' * f - v' * g) := by ring
    rw [e]
    exact W.sub_mem (W.mul_mem_left _ huv) (W.mul_mem_left _ (hPW huv'))
  have hdiff : u * v' - u' * v ∈ U :=
    hWU' ((hWp.mem_or_mem hmem).resolve_left hV.den_not_mem)
  have hv'U : v' ∈ U := hDU hv'D
  have hu'v : u' * v ∈ U := by
    have e : u' * v = u * v' - (u * v' - u' * v) := by ring
    rw [e]
    exact U.sub_mem (U.mul_mem_left _ hv'U) hdiff
  exact (hUp.mem_or_mem hu'v).elim hu' hv
end RightTermSupport
end GroundTheory.Heights₂.Heights.NumbersDVR
