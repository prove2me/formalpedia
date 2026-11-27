-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpStrictTransform_proof_7636b51a728d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:04:59.583546+00:00
-- url     : https://prove2.me/submissions/ddd85090-48fd-4dff-a37d-f5e598205f6d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AevalChartSubstMemOfMemBlowUpOf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_liftForm_b9c03287c289
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_mem_of_mem_blowUpOf_bf1aac77e819
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_of_aeval_chartSubst_mem_baae11dd03d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_relation_be2eb66028dd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpCof_spec_933dc8cb6ebe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUp_offSpecial_dfd3fde00b14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_liftForm_facts_3c10203679d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_ne_top_a831a4f25617
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_C_d98d1f1a22f5


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
namespace BlowUpStrictTransform
theorem _root_.solution : BlowUpStrictTransform.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD s hsP e m H hϖH hH
  set Q := blowUpOf P (blowUpGens s g f m e) with hQ
  have hPp : P.IsPrime := hP.multiProj.isPrime

  obtain ⟨x, hx, hHmin⟩ : ∃ x : MRing (extIdx ι (BlowUpIdx ι)) O,
      (x = liftForm s ∨ x = newVar none) ∧ H ∈ (Q ⊔ Ideal.span {x}).minimalPrimes := by
    have hm : ∀ {F}, divCycle Q F H ≠ 0 → H ∈ (Q ⊔ Ideal.span {F}).minimalPrimes := by
      intro F hF
      unfold divCycle at hF
      split_ifs at hF with hW
      · exact hW.1
      · exact absurd rfl hF
    rcases hH with hH | hH
    · exact ⟨_, Or.inl rfl, hm hH⟩
    · exact ⟨_, Or.inr rfl, hm hH⟩
  obtain ⟨hHp, hQH, hHrel⟩ : H.IsPrime ∧ Q ≤ H ∧ IsRelevant H := by
    rcases hH with hH | hH
    · exact le_and_isRelevant_of_divCycle_ne_zero hH
    · exact le_and_isRelevant_of_divCycle_ne_zero hH
  have mnm : ∀ {y z}, y ∉ H → z ∉ H → y * z ∉ H := fun hy hz hyz => (hHp.mem_or_mem hyz).elim hy hz
  have hxH : x ∈ H := hHmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  set H₀ := H.comap (liftForm (J := BlowUpIdx ι)) with hH₀
  obtain ⟨hH₀p, hPH₀, hrel₀, -⟩ := comap_liftForm_facts hHp hQH hHrel
  have hϖH₀ : (C ϖ : MRing ι O) ∉ H₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖH

  obtain ⟨u₀, v₀, hu, hv, h⟩ := hD.unit_off_special H₀ hH₀p hPH₀ hrel₀ hϖH₀
  obtain ⟨i, hpm, hYi, -⟩ := blowUp_offSpecial hPp e hD.den_not_mem hHp hQH hHrel (u₀ := u₀) hv h
  set a := blowUpCof s m e u₀ v₀ with ha_def
  have haS : liftForm (a (some (some i))) ∉ H := by
    show liftForm (v₀ * powMonomial e i) ∉ H
    rw [map_mul]; exact mnm hv hpm
  have hrelH : ∀ j, newVar j * liftForm (a (some (some i))) -
      newVar (some (some i)) * liftForm (a j) ∈ H :=
    fun j => hQH (blowUpCof_relation hPp e hD.den_not_mem h j _)

  have hsH₀ : s ∈ H₀ := by
    rcases hx with rfl | rfl
    · exact hxH
    · have h3 := H.sub_mem (H.mul_mem_right (liftForm (a (some (some i)))) hxH) (hrelH none)
      rw [sub_sub_cancel] at h3
      have h4 : liftForm (u₀ * s) ∈ H := (hHp.mem_or_mem h3).resolve_left hYi
      rw [map_mul] at h4
      exact (hHp.mem_or_mem h4).resolve_left hu

  have hmin₀ : H₀ ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
    refine ⟨⟨hH₀p, sup_le hPH₀ ((Ideal.span_singleton_le_iff_mem _).mpr hsH₀)⟩,
      fun P' hP' hP'H₀ => ?_⟩
    have := hP'.1
    have hsP' : s ∈ P' := hP'.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    let Q' := (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P').comap
      (aeval (R := O) (chartSubst a))
    have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
    have hQQ' : Q ⊔ Ideal.span {x} ≤ Q' := by
      refine sup_le (fun F hF => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      · exact Ideal.map_mono (le_sup_left.trans hP'.2)
          (aeval_chartSubst_mem_of_mem_blowUpOf hPp hD.den_not_mem (fun j => blowUpCof_spec e h j) hF)
      · rw [Ideal.mem_comap]
        rcases hx with rfl | rfl
        · rw [aeval_chartSubst_liftForm]
          exact Ideal.mem_map_of_mem _ hsP'
        · simp only [newVar, aeval_X, chartSubst]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (P'.mul_mem_left _ hsP'))
    have hQ'H : Q' ≤ H := fun F hF => mem_of_aeval_chartSubst_mem hHp hP'H₀ _ haS hrelH hF
    have hHQ' := hHmin.2 ⟨hQ'p, hQQ'⟩ hQ'H
    intro p hp
    have h5 : Polynomial.C p ∈ Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P' := by
      rw [← aeval_chartSubst_liftForm a p]
      exact hHQ' hp
    simpa using Ideal.mem_map_C_iff.mp h5 0

  have := hH₀p
  unfold divCycle
  rw [dif_pos ⟨hmin₀, hrel₀⟩]
  have hne := length_localizedQuot_ne_top (P ⊔ Ideal.span {s}) H₀ hmin₀
  have hnz : multAt (P ⊔ Ideal.span {s}) H₀ ≠ 0 := by
    unfold multAt
    rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
    intro hs
    obtain ⟨r, hr, hr0⟩ := hs (Ideal.Quotient.mk _ 1)
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hr0
    exact hr (hmin₀.1.2 hr0)
  have htn : (multAt (P ⊔ Ideal.span {s}) H₀).toNat ≠ 0 :=
    fun h0 => (ENat.toNat_eq_zero.mp h0).elim hnz hne
  exact_mod_cast htn
end BlowUpStrictTransform
end GroundTheory.Heights₂.Heights.NumbersDVR
