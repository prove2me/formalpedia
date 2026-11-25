-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_linearIndependent_of_not_mem_98e9524d2579
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:16.144815+00:00
-- url     : https://prove2.me/submissions/ecde362d-1023-4536-abb8-7e681929d6bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairIff

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
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
universe u v w
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
theorem _root_.solution {Vs : Fin (N + 1) → Submodule Ω E} (mono : Monotone Vs)
    {gen : Fin N → E} (hmem : ∀ i, gen i ∈ Vs i.succ) (hnot : ∀ i, gen i ∉ Vs i.castSucc) :
    LinearIndependent Ω gen := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  by_contra hne
  push Not at hne
  set S := Finset.univ.filter (fun q : Fin N => a q ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨q, hq⟩ := hne
    exact ⟨q, by simp [hS, hq]⟩
  set i := S.max' hSne
  have hi : a i ≠ 0 := by
    have := S.max'_mem hSne
    simpa [hS] using this
  have hrest : ∑ q ∈ Finset.univ.erase i, a q • gen q ∈ Vs i.castSucc := by
    refine Submodule.sum_mem _ fun q hq => ?_
    by_cases haq : a q = 0
    · rw [haq, zero_smul]
      exact Submodule.zero_mem _
    · have hle : q ≤ i := S.le_max' q (by simp [hS, haq])
      have hlt : q < i := lt_of_le_of_ne hle (Finset.ne_of_mem_erase hq)
      exact Submodule.smul_mem _ _ (mono (Fin.le_def.mpr (by simp; omega)) (hmem q))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at ha
  have hai : a i • gen i ∈ Vs i.castSucc := by
    rw [eq_neg_of_add_eq_zero_left ha]
    exact Submodule.neg_mem _ hrest
  apply hnot i
  have := Submodule.smul_mem _ (a i)⁻¹ hai
  rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at this
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
