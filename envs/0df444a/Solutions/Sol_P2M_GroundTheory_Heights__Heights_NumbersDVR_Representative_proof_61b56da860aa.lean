-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_Representative_proof_61b56da860aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:27:38.526514+00:00
-- url     : https://prove2.me/submissions/5b6f50b0-697a-4a0f-aa37-ada56306e2aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_pair_b1860578b0d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_separator_d6cdd5665e0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_not_mem_of_isRelevant_8f453759efa5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_sub_mem_79374b1d92c7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_of_unit_off_special_da747d91115e


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
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace Representative
theorem _root_.solution (h1 : DivCycleMul.Statement.{u}) : Representative.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P b f g hP hV T hT
  classical
  haveI := hP.isPrime
  obtain ⟨bf, bg, hbf, hbg, hb⟩ := hV.degrees
  have claim : ∃ f₁ g₁ : MRing ι O, (∃ F E : K → ℕ, IsMultiHomog f₁ F ∧ IsMultiHomog g₁ E ∧
      (fun k => (F k : ℤ) - E k) = b) ∧ f₁ ∉ P ∧ g₁ ∉ P ∧ f₁ * g - g₁ * f ∈ P ∧
      ∀ H ∈ T, f₁ ∉ H ∧ g₁ ∉ H := by
    rcases T.eq_empty_or_nonempty with hTe | ⟨H₀, hH₀⟩
    · refine ⟨f, g, ⟨bf, bg, hbf, hbg, hb⟩, hV.num_not_mem, hV.den_not_mem, ?_, by simp [hTe]⟩
      rw [mul_comm, sub_self]
      exact P.zero_mem

    set T' := T.filter (fun H => ∀ H' ∈ T, H ≤ H' → H' = H) with hT'
    have hmax : ∀ H ∈ T, ∃ H' ∈ T', H ≤ H' := by
      intro H hH
      obtain ⟨H', hle, hm⟩ := T.exists_le_maximal hH
      exact ⟨H', Finset.mem_filter.mpr ⟨hm.1, fun H'' hH'' hle' => le_antisymm (hm.2 hH'' hle') hle'⟩,
        hle⟩
    obtain ⟨H₁, hH₁, -⟩ := hmax H₀ hH₀
    have hdata : ∀ H, ∃ (a u v : MRing ι O) (A e d : K → ℕ), H ∈ T' →
        (IsMultiHomog a A ∧ a ∉ H ∧ (∀ H' ∈ T', H' ≠ H → a ∈ H') ∧ IsMultiHomog u e ∧
          IsMultiHomog v d ∧ d + bg = e + bf ∧ u ∉ H ∧ v ∉ H ∧ u * f - v * g ∈ P) := by
      intro H
      by_cases hH : H ∈ T'
      · have hHT := (Finset.mem_filter.mp hH).1
        obtain ⟨hH1, hPH, hϖH, -⟩ := hT H hHT
        haveI := hH1.isPrime
        obtain ⟨u0, v0, hu0, hv0, h0⟩ :=
          hV.unit_off_special H hH1.isPrime hPH hH1.relevant hϖH
        obtain ⟨u, v, e, d, hu, hv, hde, huH, hvH, huv⟩ := exists_form_pair hP.multiHomog hPH hbf hbg
          hV.num_not_mem hV.den_not_mem hu0 hv0 h0
        obtain ⟨a, A, ha, haH, haS⟩ := exists_form_separator (H := H) (T'.erase H)
          (fun H' hH' => ⟨(hT H' (Finset.mem_filter.mp (Finset.mem_of_mem_erase hH')).1).1.multiHomog,
            fun hle => Finset.ne_of_mem_erase hH'
              ((Finset.mem_filter.mp (Finset.mem_of_mem_erase hH')).2 H hHT hle).symm⟩)
        exact ⟨a, u, v, A, e, d, fun _ => ⟨ha, haH,
          fun H' hH' hne => haS H' (Finset.mem_erase.mpr ⟨hne, hH'⟩), hu, hv, hde, huH, hvH, huv⟩⟩
      · exact ⟨0, 0, 0, 0, 0, 0, fun h => absurd h hH⟩
    choose a u v A e d hprop using hdata
    set E : K → ℕ := ∑ H ∈ T', (A H + e H) with hE
    have hmono : ∀ H, ∃ m : MRing ι O, H ∈ T' → IsMultiHomog m (E - (A H + e H)) ∧ m ∉ H := by
      intro H
      by_cases hH : H ∈ T'
      · obtain ⟨hH1, -⟩ := hT H (Finset.mem_filter.mp hH).1
        haveI := hH1.isPrime
        obtain ⟨m, hm⟩ := exists_form_not_mem_of_isRelevant hH1.relevant (E - (A H + e H))
        exact ⟨m, fun _ => hm⟩
      · exact ⟨0, fun h => absurd h hH⟩
    choose m hm using hmono
    have hle : ∀ H ∈ T', A H + e H ≤ E := fun H hH =>
      Finset.single_le_sum (f := fun H => A H + e H) (fun _ _ _ => Nat.zero_le _) hH
    set F : K → ℕ := A H₁ + (E - (A H₁ + e H₁)) + d H₁ with hF
    have hFeq : F + bg = E + bf := by
      obtain ⟨-, -, -, -, -, hde, -⟩ := hprop H₁ hH₁
      funext k
      have h1k := hle H₁ hH₁ k
      have h2k := congrFun hde k
      simp only [Pi.add_apply, Pi.sub_apply] at h1k h2k ⊢
      simp only [hF, Pi.add_apply, Pi.sub_apply]
      omega
    have hdegv : ∀ H ∈ T', A H + (E - (A H + e H)) + d H = F := by
      intro H hH
      obtain ⟨-, -, -, -, -, hde, -⟩ := hprop H hH
      funext k
      have h1k := hle H hH k
      have h2k := congrFun hde k
      have h3k := congrFun hFeq k
      simp only [Pi.add_apply, Pi.sub_apply] at h1k h2k h3k ⊢
      omega
    have hdegu : ∀ H ∈ T', A H + (E - (A H + e H)) + e H = E := by
      intro H hH
      funext k
      have h1k := hle H hH k
      simp only [Pi.add_apply, Pi.sub_apply] at h1k ⊢
      omega
    have hnot : ∀ H ∈ T', (∑ H' ∈ T', a H' * m H' * v H') ∉ H ∧
        (∑ H' ∈ T', a H' * m H' * u H') ∉ H := by
      intro H hH
      obtain ⟨hH1, -⟩ := hT H (Finset.mem_filter.mp hH).1
      have hp := hH1.isPrime
      obtain ⟨-, haH, -, -, -, -, huH, hvH, -⟩ := hprop H hH
      have hrest : ∀ w : Ideal (MRing ι O) → MRing ι O,
          (∑ H' ∈ T'.erase H, a H' * m H' * w H') ∈ H := fun w =>
        H.sum_mem fun H' hH' => H.mul_mem_right _ (H.mul_mem_right _
          ((hprop H' (Finset.mem_of_mem_erase hH')).2.2.1 H hH (Finset.ne_of_mem_erase hH').symm))
      have hone : ∀ w : Ideal (MRing ι O) → MRing ι O, w H ∉ H →
          (∑ H' ∈ T', a H' * m H' * w H') ∉ H := by
        intro w hw hmem
        rw [← Finset.add_sum_erase T' _ hH] at hmem
        have h' := (Submodule.add_mem_iff_left _ (hrest w)).mp hmem
        rcases hp.mem_or_mem h' with h'' | h''
        · rcases hp.mem_or_mem h'' with h''' | h'''
          · exact haH h'''
          · exact (hm H hH).2 h'''
        · exact hw h''
      exact ⟨hone v hvH, hone u huH⟩
    refine ⟨∑ H ∈ T', a H * m H * v H, ∑ H ∈ T', a H * m H * u H, ⟨F, E, ?_, ?_, ?_⟩,
      fun h' => (hnot H₁ hH₁).1 (((hT H₁ (Finset.mem_filter.mp hH₁).1).2.1) h'),
      fun h' => (hnot H₁ hH₁).2 (((hT H₁ (Finset.mem_filter.mp hH₁).1).2.1) h'), ?_, ?_⟩
    · refine IsWeightedHomogeneous.sum _ _ _ fun H hH => ?_
      obtain ⟨ha, -, -, -, hv, -⟩ := hprop H hH
      have h' := (ha.mul (hm H hH).1).mul hv
      rwa [hdegv H hH] at h'
    · refine IsWeightedHomogeneous.sum _ _ _ fun H hH => ?_
      obtain ⟨ha, -, -, hu, -⟩ := hprop H hH
      have h' := (ha.mul (hm H hH).1).mul hu
      rwa [hdegu H hH] at h'
    · rw [← hb]
      funext k
      have hk := congrFun hFeq k
      simp only [Pi.add_apply] at hk
      omega
    · rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine P.sum_mem fun H hH => ?_
      obtain ⟨-, -, -, -, -, -, -, -, huv⟩ := hprop H hH
      have e2 : a H * m H * v H * g - a H * m H * u H * f = -(a H * m H) * (u H * f - v H * g) := by
        ring
      rw [e2]
      exact P.mul_mem_left _ huv
    · intro H hH
      obtain ⟨H', hH', hle'⟩ := hmax H hH
      exact ⟨fun h' => (hnot H' hH').1 (hle' h'), fun h' => (hnot H' hH').2 (hle' h')⟩
  obtain ⟨f₁, g₁, hdeg, hf₁, hg₁, hmem, hT₁⟩ := claim
  have hunitP : ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W →
      (C ϖ : MRing ι O) ∉ W → ∃ u v : MRing ι O, u ∉ W ∧ v ∉ W ∧ u * f₁ - v * g₁ ∈ P := by
    intro W hW hPW hrel hϖW
    obtain ⟨u, v, hu, hv, h⟩ := hV.unit_off_special W hW hPW hrel hϖW
    refine ⟨u, v, hu, hv, ?_⟩
    have e2 : g * (u * f₁ - v * g₁) = u * (f₁ * g - g₁ * f) + g₁ * (u * f - v * g) := by ring
    have h' : g * (u * f₁ - v * g₁) ∈ P := by
      rw [e2]
      exact P.add_mem (P.mul_mem_left _ hmem) (P.mul_mem_left _ h)
    exact (hP.isPrime.mem_or_mem h').resolve_left hV.den_not_mem
  refine ⟨f₁, g₁, IsVerticalDivisor.of_unit_off_special hdeg hf₁ hg₁ hunitP, ?_, fun H hH => ?_⟩
  · have hx := h1 O K ι P f₁ g hP.isPrime hf₁ hV.den_not_mem
    have hy := h1 O K ι P g₁ f hP.isPrime hg₁ hV.num_not_mem
    have hxy : divCycle P (f₁ * g) = divCycle P (g₁ * f) := divCycle_eq_of_sub_mem hmem
    funext W
    have h' := congrFun (hx.symm.trans (hxy.trans hy)) W
    simp only [Pi.add_apply] at h'
    unfold ratDiv
    linarith
  · obtain ⟨hH1, hPH, -, -⟩ := hT H hH
    exact IsVerticalDivisor.of_unit_off_special hdeg (hT₁ H hH).1 (hT₁ H hH).2
      fun W hW hHW hrel hϖW =>
        let ⟨u, v, hu, hv, h⟩ := hunitP W hW (hPH.trans hHW) hrel hϖW
        ⟨u, v, hu, hv, hPH h⟩
end Representative
end GroundTheory.Heights₂.Heights.NumbersDVR
