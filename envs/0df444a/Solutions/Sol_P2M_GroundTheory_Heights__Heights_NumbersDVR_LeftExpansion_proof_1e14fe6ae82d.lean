-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_LeftExpansion_proof_1e14fe6ae82d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:07:21.850682+00:00
-- url     : https://prove2.me/submissions/81680119-e45f-4537-84e1-d01317569e96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WithBotLtNatCastOfAddOneLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_nontrivial_of_le_182d81799d11
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_natCast_of_add_one_le_e987da8e2e4c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimStrictDrop_proof_15777780f510
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleFiniteSupport_proof_010201f3d63e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleMul_proof_5282581d8898
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialQuotDim_proof_5536281ab8d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SupSpanMultiHomog_proof_861d53cbe2c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_ne_top_a831a4f25617
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace LeftExpansion
theorem _root_.solution (hcut : VNumCut.Statement.{u}) : LeftExpansion.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hno L
  classical
  have : P.IsPrime := hP.multiProj.isPrime

  have key : ∀ G, ratDiv P f g G ≠ 0 →
      vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L) = cycEval (fun U => vNum U L) (divCycle G s) := by
    intro G hG
    have hmin : ∃ h : MRing ι O, h ∉ P ∧ (∃ e : K → ℕ, IsMultiHomog h e) ∧
        G ∈ (P ⊔ Ideal.span {h}).minimalPrimes ∧ IsRelevant G := by
      obtain ⟨bf, bg, hf, hg, -⟩ := hD.degrees
      by_cases hfG : divCycle P f G = 0
      · have hgG : divCycle P g G ≠ 0 := by
          intro h0
          apply hG
          simp [ratDiv, hfG, h0]
        unfold divCycle at hgG
        split_ifs at hgG with hW
        · exact ⟨g, hD.den_not_mem, ⟨bg, hg⟩, hW.1, hW.2⟩
        · exact absurd rfl hgG
      · unfold divCycle at hfG
        split_ifs at hfG with hW
        · exact ⟨f, hD.num_not_mem, ⟨bf, hf⟩, hW.1, hW.2⟩
        · exact absurd rfl hfG
    obtain ⟨h, hhP, ⟨e, he⟩, hGmin, hGrel⟩ := hmin
    have hGp : G.IsPrime := hGmin.1.1
    have hPG : P ≤ G := le_sup_left.trans hGmin.1.2
    have hhG : h ∈ G := hGmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hPltG : P < G := lt_of_le_of_ne hPG (fun hPeq => hhP (hPeq ▸ hhG))
    have hGmh : IsMultiHomogIdeal G :=
      MinimalPrimeMultiHomog.proof O K ι _ G
        (SupSpanMultiHomog.proof O K ι P h e hP.multiProj.multiHomog he) hGmin
    have hϖG : (C ϖ : MRing ι O) ∈ G := hD.vertical G hG
    have hdim : ringKrullDim (MRing ι O ⧸ G) < ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      have hdrop := DimStrictDrop.proof (MRing ι O) P G hPltG
      rw [hP.dim] at hdrop
      have hN : d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K := by omega
      rw [hN] at hdrop
      exact withBot_lt_natCast_of_add_one_le _ _ hdrop
    have hsG : s ∉ G := by
      intro hsG
      have h1 := mem_minimalPrimes_sup_span_mul (x := h) hsP hGmin
      have hGs : G ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
        refine ⟨⟨hGp, sup_le hPG ((Ideal.span_singleton_le_iff_mem _).mpr hsG)⟩, fun Q hQ hQG => ?_⟩
        have hsQ : s ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
        exact h1.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2)
          ((Ideal.span_singleton_le_iff_mem _).mpr (Q.mul_mem_left h hsQ))⟩ hQG
      have hne : divCycle P s G ≠ 0 := by
        unfold divCycle
        rw [dif_pos ⟨hGs, hGrel⟩]
        have := localizedQuot_nontrivial_of_le (P ⊔ Ideal.span {s}) G hGs.1.2
        have h0 : multAt (P ⊔ Ideal.span {s}) G ≠ 0 :=
          (Module.length_pos (R := Localization.AtPrime G)
            (M := LocalizedModule G.primeCompl (MRing ι O ⧸ (P ⊔ Ideal.span {s})))).ne'
        have htop := length_localizedQuot_ne_top _ G hGs
        exact_mod_cast (ENat.toNat_pos h0 htop).ne'
      exact hG (hno G hϖG hne)
    exact hcut O ϖ hϖ K ι G d hGp hGmh hϖG hdim s c hs hsG L

  have hfinR : (Function.support (ratDiv P f g)).Finite :=
    ((DivCycleFiniteSupport.proof O K ι P f).union (DivCycleFiniteSupport.proof O K ι P g)).subset
      (fun G hG => by
        by_contra hc
        simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
        exact hG (by simp [ratDiv, hc.1, hc.2]))
  set A := hfinR.toFinset with hAdef
  have hfinB : (⋃ G ∈ A, Function.support (divCycle G s)).Finite :=
    A.finite_toSet.biUnion (fun G _ => DivCycleFiniteSupport.proof O K ι G s)
  set B := hfinB.toFinset with hBdef
  have hA : ∀ G, ratDiv P f g G ≠ 0 → G ∈ A := fun G hG => hfinR.mem_toFinset.mpr hG
  have hB : ∀ G ∈ A, ∀ U, divCycle G s U ≠ 0 → U ∈ B :=
    fun G hGA U hU => hfinB.mem_toFinset.mpr (Set.mem_biUnion hGA hU)
  have eL : cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
      ∑ G ∈ A, ∑ U ∈ B, ratDiv P f g G * divCycle G s U * vNum U L := by
    unfold cycEval
    rw [finsum_eq_sum_of_support_subset _ (s := A) (fun G hG => hA G (left_ne_zero_of_mul hG))]
    refine Finset.sum_congr rfl fun G _ => ?_
    by_cases hr : ratDiv P f g G = 0
    · simp [hr]
    · rw [key G hr, cycEval, finsum_eq_sum_of_support_subset _ (s := B)
        (fun U hU => hB G (hA G hr) U (left_ne_zero_of_mul hU)), Finset.mul_sum]
      exact Finset.sum_congr rfl fun U _ => by ring
  have eR : cycEval (fun U => vNum U L) (fun U => cycEval (fun G => divCycle G s U) (ratDiv P f g)) =
      ∑ U ∈ B, ∑ G ∈ A, ratDiv P f g G * divCycle G s U * vNum U L := by
    unfold cycEval
    have hsub : Function.support (fun U =>
        (∑ᶠ G, ratDiv P f g G * divCycle G s U) * vNum U L) ⊆ ↑B := by
      intro U hU
      have h1 := left_ne_zero_of_mul hU
      obtain ⟨G, hG⟩ : ∃ G, ratDiv P f g G * divCycle G s U ≠ 0 := by
        by_contra hc
        push Not at hc
        exact h1 (finsum_eq_zero_of_forall_eq_zero hc)
      exact hB G (hA G (left_ne_zero_of_mul hG)) U (right_ne_zero_of_mul hG)
    rw [finsum_eq_sum_of_support_subset _ hsub]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [finsum_eq_sum_of_support_subset _ (s := A) (fun G hG => hA G (left_ne_zero_of_mul hG)),
      Finset.sum_mul]
  rw [eL, eR, Finset.sum_comm]
end LeftExpansion
end GroundTheory.Heights₂.Heights.NumbersDVR
