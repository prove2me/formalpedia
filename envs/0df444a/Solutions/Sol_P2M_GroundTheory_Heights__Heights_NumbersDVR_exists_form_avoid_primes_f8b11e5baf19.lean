-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_avoid_primes_f8b11e5baf19
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:55.119152+00:00
-- url     : https://prove2.me/submissions/8af8044a-4140-4017-b3e4-0b316b499624

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_RelevantMinimalOfDivCycleNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_not_mem_of_isRelevant_8f453759efa5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_separator_d6cdd5665e0a


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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (S : Finset (Ideal (MRing ι R)))
    (hS : ∀ W ∈ S, W.IsPrime ∧ IsMultiHomogIdeal W ∧ IsRelevant W) (e₀ : K → ℕ) :
    ∃ (e : K → ℕ) (h : MRing ι R), IsMultiHomog h e ∧ e₀ ≤ e ∧ ∀ W ∈ S, h ∉ W := by
  classical
  set T := S.filter (fun W => ∀ W' ∈ S, W ≤ W' → W' = W) with hT
  have hTS : ∀ W ∈ T, W ∈ S := fun W hW => (Finset.mem_filter.mp hW).1
  have hTmax : ∀ W ∈ T, ∀ W' ∈ S, W ≤ W' → W' = W := fun W hW => (Finset.mem_filter.mp hW).2
  have hle : ∀ W ∈ S, ∃ W' ∈ T, W ≤ W' := by
    intro W hW
    obtain ⟨W', hWW', hW'⟩ := (S.finite_toSet).exists_le_maximal hW
    exact ⟨W', Finset.mem_filter.mpr ⟨hW'.prop, fun W'' hW'' h => le_antisymm (hW'.2 hW'' h) h⟩, hWW'⟩
  have hsep : ∀ W ∈ T, ∃ (a : MRing ι R) (A : K → ℕ), IsMultiHomog a A ∧ a ∉ W ∧
      ∀ W' ∈ T.erase W, a ∈ W' := by
    intro W hW
    have := (hS W (hTS W hW)).1
    refine exists_form_separator (T.erase W) fun W' hW' => ⟨(hS W' (hTS W' (Finset.mem_of_mem_erase hW'))).2.1,
      fun hle' => Finset.ne_of_mem_erase hW' ?_⟩
    exact (hTmax W' (Finset.mem_of_mem_erase hW') W (hTS W hW) hle').symm
  choose! a A haH haW haMem using hsep
  set e : K → ℕ := e₀ + ∑ W ∈ T, A W with he
  have hAe : ∀ W ∈ T, A W ≤ e := fun W hW =>
    le_add_left (Finset.single_le_sum (f := A) (fun _ _ => fun _ => Nat.zero_le _) hW)
  have hmon : ∀ W ∈ T, ∃ m : MRing ι R, IsMultiHomog m (e - A W) ∧ m ∉ W := by
    intro W hW
    have := (hS W (hTS W hW)).1
    exact exists_form_not_mem_of_isRelevant (hS W (hTS W hW)).2.2 _
  choose! m hmH hmW using hmon
  refine ⟨e, ∑ W ∈ T, a W * m W, ?_, le_self_add, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun W hW => ?_
    have := (haH W hW).mul (hmH W hW)
    rwa [add_tsub_cancel_of_le (hAe W hW)] at this
  · have key : ∀ W₀ ∈ T, (∑ W ∈ T, a W * m W) ∉ W₀ := by
      intro W₀ hW₀ hmem
      have hp := (hS W₀ (hTS W₀ hW₀)).1
      rw [← Finset.add_sum_erase _ _ hW₀] at hmem
      have hrest : (∑ W ∈ T.erase W₀, a W * m W) ∈ W₀ :=
        Ideal.sum_mem _ fun W hW => Ideal.mul_mem_right _ _ (haMem W (Finset.mem_of_mem_erase hW) W₀
          (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hW).symm, hW₀⟩))
      rcases hp.mem_or_mem ((Ideal.add_mem_iff_left _ hrest).mp hmem) with h2 | h2
      · exact haW W₀ hW₀ h2
      · exact hmW W₀ hW₀ h2
    intro W hW hmem
    obtain ⟨W', hW', hle'⟩ := hle W hW
    exact key W' hW' (hle' hmem)
end GroundTheory.Heights₂.Heights.NumbersDVR
