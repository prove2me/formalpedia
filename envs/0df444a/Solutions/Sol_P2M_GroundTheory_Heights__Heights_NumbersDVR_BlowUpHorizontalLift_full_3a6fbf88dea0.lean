-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpHorizontalLift_full_3a6fbf88dea0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:03:52.763398+00:00
-- url     : https://prove2.me/submissions/c4858ac1-fd26-4e4c-b328-ce6f90e840ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AevalChartSubstMemOfMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalLift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_liftForm_b9c03287c289
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_mem_of_mem_blowUpOf_bf1aac77e819
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_ne_top_a831a4f25617
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_C_d98d1f1a22f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_X_709b97b21fde
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mem_blowUpOf_d5667072f554
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_blowUpOf_of_sub_30a04624d21b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_aeval_chartSubst_mem_baae11dd03d9


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
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace BlowUpHorizontalLift
theorem _root_.solution : BlowUpHorizontalLift.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime
  obtain ⟨hWp, hPW, hrelW⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have hWmin : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  have hxW : x ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  obtain ⟨j₀, hj₀⟩ := hloc W hWp hPW hrelW hϖW
  choose v w hvW hvw using hj₀

  have hu₀ : u j₀ ∉ P := by
    intro h0
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have h2 := P.add_mem (hvw j) (P.mul_mem_left (w j) h0)
      rwa [sub_add_cancel] at h2
    rcases hPp.mem_or_mem h1 with h2 | h2
    · exact hvW j (hPW h2)
    · exact hj h2

  set V : MRing ι O := ∏ j, v j with hV
  set a : J → MRing ι O := fun j => w j * ∏ i ∈ Finset.univ.erase j, v i with ha_def
  have hVW : V ∉ W := by
    intro h
    obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hvW j hj
  have ha : ∀ j, V * u j - u j₀ * a j ∈ P := by
    intro j
    have e : V * u j - u j₀ * a j = (∏ i ∈ Finset.univ.erase j, v i) * (v j * u j - w j * u j₀) := by
      simp only [hV, ha_def]
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]
      ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hVa : V - a j₀ ∈ P := by
    have h1 : (V - a j₀) * u j₀ ∈ P := by
      have h2 := ha j₀
      rwa [show V * u j₀ - u j₀ * a j₀ = (V - a j₀) * u j₀ by ring] at h2
    exact (hPp.mem_or_mem h1).resolve_right hu₀
  have haW : a j₀ ∉ W := fun h => hVW (by simpa using W.add_mem (hPW hVa) h)

  set Wt : Ideal (MRing (extIdx ι J) O) :=
    (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) W).comap
      (aeval (R := O) (chartSubst a)) with hWt
  have hWtp : Wt.IsPrime := Ideal.comap_isPrime _ _
  have hcomap : ∀ s, liftForm (J := J) s ∈ Wt ↔ s ∈ W := by
    intro s
    rw [hWt, Ideal.mem_comap, aeval_chartSubst_liftForm]
    constructor
    · intro h
      simpa using Ideal.mem_map_C_iff.mp h 0
    · intro h
      exact Ideal.mem_map_of_mem _ h
  have hBWt : blowUpOf P u ≤ Wt := fun F hF =>
    Ideal.map_mono hPW (aeval_chartSubst_mem_of_mem_blowUpOf hPp hu₀ ha hF)
  have hxWt : liftForm x ∈ Wt := (hcomap x).2 hxW
  have hrelWt : IsRelevant Wt := by
    rintro (_ | k)
    · refine ⟨j₀, fun h => haW ?_⟩
      rw [hWt, Ideal.mem_comap] at h
      simp only [aeval_X, chartSubst] at h
      simpa using Ideal.mem_map_C_iff.mp h 1
    · obtain ⟨i, hi⟩ := hrelW k
      refine ⟨i, fun h => hi ((hcomap _).1 ?_)⟩
      rw [liftForm_X]
      exact h

  have hmin : Wt ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    refine ⟨⟨hWtp, sup_le hBWt ((Ideal.span_singleton_le_iff_mem _).mpr hxWt)⟩, fun Q hQ hQWt => ?_⟩
    have hQp := hQ.1
    have hBQ : blowUpOf P u ≤ Q := le_sup_left.trans hQ.2
    have hxQ : liftForm x ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hle : Q.comap (liftForm (J := J)) ≤ W := fun s hs => (hcomap s).1 (hQWt hs)
    have hQ₀ : Q.comap (liftForm (J := J)) = W :=
      le_antisymm hle (hWmin.2 ⟨Ideal.comap_isPrime _ _,
        sup_le (fun p hp => hBQ (liftForm_mem_blowUpOf hp))
          ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)⟩ hle)
    intro F hF
    refine mem_of_aeval_chartSubst_mem hQp hQ₀.ge j₀ (fun h => haW ?_) (fun j => hBQ ?_) hF
    · rw [← hQ₀]
      exact h
    · apply mem_blowUpOf_of_sub
      have e : u j * a j₀ - u j₀ * a j = (V * u j - u j₀ * a j) - u j * (V - a j₀) := by ring
      rw [e]
      exact P.sub_mem (ha j) (P.mul_mem_left _ hVa)
  refine ⟨Wt, ?_, fun h => hϖW ((hcomap _).1 (by rw [liftForm_C]; exact h)), ?_⟩
  ·
    unfold divCycle
    rw [dif_pos ⟨hmin, hrelWt⟩]
    have hne := length_localizedQuot_ne_top (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt hmin
    have hnz : multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt ≠ 0 := by
      unfold multAt
      rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
      intro hs
      obtain ⟨r, hr, hr0⟩ := hs (Ideal.Quotient.mk _ 1)
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
        Ideal.Quotient.eq_zero_iff_mem] at hr0
      exact hr (hmin.1.2 hr0)
    have htn : (multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt).toNat ≠ 0 :=
      fun h0 => (ENat.toNat_eq_zero.mp h0).elim hnz hne
    exact_mod_cast htn
  · ext s
    rw [Ideal.mem_comap]
    exact hcomap s
end BlowUpHorizontalLift
end GroundTheory.Heights₂.Heights.NumbersDVR
