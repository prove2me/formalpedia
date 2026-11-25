-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_866e61ad51fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:58:05.415185+00:00
-- url     : https://prove2.me/submissions/230e820d-84b4-4511-b432-87ac6c11555e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_xProd_ne_zero_5c3b01ddff8c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_isHomogeneous_4a7cd1fe755c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_mem_monos_27cdb6de9abb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_aeval_monoProd_6aa38ad48f99

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
theorem _root_.solution (I J : Chart x) {c : Ω} (hc : c ∈ chartRing S x (unionChart I J)) :
    ∃ D : ℕ, chartRatio I J ^ D * c ∈ chartRing S x I := by
  classical
  have := (algebraMap S Ω).domain_nontrivial
  obtain ⟨i₀, hi₀⟩ := I.2.1
  have hx₀ : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  obtain ⟨a, ha⟩ : ∃ a, I.1.card = a + 1 :=
    ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos I.2.1.card_pos).symm⟩
  obtain ⟨b, hb⟩ : ∃ b, J.1.card = b + 1 :=
    ⟨J.1.card - 1, (Nat.succ_pred_eq_of_pos J.2.1.card_pos).symm⟩
  have hI0 : ∏ i ∈ I.1, x i ≠ 0 := xProd_ne_zero I

  have hWmul : ∀ w w' : Ω, (∃ D : ℕ, chartRatio I J ^ D * w ∈ chartRing S x I) →
      (∃ D : ℕ, chartRatio I J ^ D * w' ∈ chartRing S x I) →
      ∃ D : ℕ, chartRatio I J ^ D * (w * w') ∈ chartRing S x I := by
    rintro w w' ⟨D, hD⟩ ⟨D', hD'⟩
    refine ⟨D + D', ?_⟩
    have e : chartRatio I J ^ (D + D') * (w * w') =
        (chartRatio I J ^ D * w) * (chartRatio I J ^ D' * w') := by ring
    rw [e]; exact mul_mem hD hD'

  have hgen : ∀ i ∈ (unionChart I J).1,
      ∃ D : ℕ, chartRatio I J ^ D * (x i₀ / x i) ∈ chartRing S x I := by
    intro i hi
    by_cases hiI : i ∈ I.1
    · refine ⟨0, X i₀, X i, 1, X_mem_monos hiI, isHomogeneous_X S i₀, isHomogeneous_X S i, ?_⟩
      simp
    · have hiJ : i ∈ J.1 := by
        rcases Finset.mem_union.mp hi with h | h
        · exact absurd h hiI
        · exact h
      have hxi : x i ≠ 0 := (mem_support x).mp (J.2.2 hiJ)
      have hcard : (J.1.erase i).card = b := by rw [Finset.card_erase_of_mem hiJ, hb]; rfl
      refine ⟨1, X i₀ * monoProd (J.1.erase i) * monoProd J.1 ^ a, monoProd I.1 ^ J.1.card,
        (a + 1) * (b + 1), pow_mem (monoProd_mem_monos subset_rfl) _, ?_, ?_, ?_⟩
      · have h1 := ((isHomogeneous_X S i₀).mul (monoProd_isHomogeneous (S := S) (J.1.erase i))).mul
          ((monoProd_isHomogeneous (S := S) J.1).pow a)
        rw [hcard, hb] at h1
        convert h1 using 1
        ring
      · have h1 := (monoProd_isHomogeneous (S := S) I.1).pow J.1.card
        rw [ha, hb] at h1
        rw [hb]
        exact h1
      · have hJ : ∏ l ∈ J.1, x l = x i * ∏ l ∈ J.1.erase i, x l :=
          (Finset.mul_prod_erase J.1 (fun l => x l) hiJ).symm
        simp only [chartRatio, xProd, map_mul, map_pow, aeval_X, aeval_monoProd, ha, hJ]
        field_simp
        ring
  have hmon : ∀ s ∈ monos (S := S) (unionChart I J).1, ∃ e : ℕ, s.IsHomogeneous e ∧
      ∃ D : ℕ, chartRatio I J ^ D * (x i₀ ^ e / aeval x s) ∈ chartRing S x I := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨i, hi, rfl⟩ := hs
      refine ⟨1, isHomogeneous_X S i, ?_⟩
      rw [pow_one, aeval_X]
      exact hgen i hi
    | one =>
      refine ⟨0, isHomogeneous_one _ _, 0, ?_⟩
      rw [pow_zero, map_one, div_one, pow_zero, one_mul]
      exact one_mem _
    | mul s s' _ _ h h' =>
      obtain ⟨e, he, hW⟩ := h
      obtain ⟨e', he', hW'⟩ := h'
      refine ⟨e + e', he.mul he', ?_⟩
      have : x i₀ ^ (e + e') / aeval x (s * s') =
          (x i₀ ^ e / aeval x s) * (x i₀ ^ e' / aeval x s') := by
        rw [pow_add, map_mul, mul_div_mul_comm]
      rw [this]
      exact hWmul _ _ hW hW'
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := hc
  obtain ⟨e', he', D, hD⟩ := hmon s hs
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (unionChart I J) hs
  have hee : e' = e := he'.inj_right hse (fun h => hs0 (by rw [h, map_zero]))
  subst hee
  refine ⟨D, ?_⟩
  have hf0 : aeval x f / x i₀ ^ e' ∈ chartRing S x I :=
    ⟨f, X i₀ ^ e', e', pow_mem (X_mem_monos hi₀) _, hf, isHomogeneous_X_pow i₀ e',
      by rw [map_pow, aeval_X]⟩
  have : chartRatio I J ^ D * (aeval x f / aeval x s) =
      (aeval x f / x i₀ ^ e') * (chartRatio I J ^ D * (x i₀ ^ e' / aeval x s)) := by
    field_simp
  rw [this]
  exact mul_mem hf0 hD
end GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
