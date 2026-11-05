-- Prove2me | solution 1 for ShortWDRODual.Legendre.lemma_2_conj
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:17:03.038762+00:00
-- url     : https://prove2.me/submissions/98efbe2e-0bb8-4706-91ef-61cc50a89c5d

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting
import Theorems.Thm_ShortWDRODual_Legendre_lemma_1

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.Legendre RWPI.SqrtLasso

theorem solution {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0) :
    let F : ℝ → EReal := fun lam => legendre (fun ρ => - robustLoss c f Phat ρ) (-lam)
    (∀ lam : ℝ, 0 ≤ lam → extIntegral Phat (fun x => (f x : EReal)) ≤ F lam) ∧
    AntitoneOn F (Set.Ici 0) ∧
    (∀ a b t : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ t → t ≤ 1 →
      F ((1 - t) * a + t * b) ≤ ((1 - t : ℝ) : EReal) * F a + ((t : ℝ) : EReal) * F b) ∧
    LowerSemicontinuousOn F (Set.Ici 0) := by
  intro F
  obtain ⟨hlb, _, _⟩ := lemma_1 Phat f c hf hfint hc hc0
  set L := robustLoss c f Phat with hL
  -- `𝓛(ρ) = −∞` for `ρ < 0`
  have hneg : ∀ ρ : ℝ, ρ < 0 → L ρ = ⊥ := by
    intro ρ hρ
    rw [hL]; unfold robustLoss
    refine le_bot_iff.mp (iSup₂_le fun P hP => ?_)
    exfalso
    have h1 : (0 : EReal) ≤ ((transportCost c Phat P : ENNReal) : EReal) := EReal.coe_ennreal_nonneg _
    have h2 : (ρ : EReal) < 0 := by exact_mod_cast hρ
    exact absurd (h1.trans hP.2) (not_le.mpr h2)
  have hnb : ∀ ρ : ℝ, 0 ≤ ρ → L ρ ≠ ⊥ := fun ρ hρ => ne_bot_of_gt (hfint.trans_le (hlb ρ hρ))
  -- the terms of the supremum
  set T : ℝ → ℝ → EReal := fun ρ lam => ((-lam * ρ : ℝ) : EReal) - -L ρ with hT
  have hF : ∀ lam, F lam = ⨆ ρ, T ρ lam := by
    intro lam; rfl
  have hTneg : ∀ ρ lam, ρ < 0 → T ρ lam = ⊥ := by
    intro ρ lam hρ
    simp only [hT]
    rw [hneg ρ hρ, EReal.neg_bot, EReal.sub_top]
  have hTtop : ∀ ρ lam, L ρ = ⊤ → T ρ lam = ⊤ := by
    intro ρ lam h
    simp only [hT]
    rw [h, EReal.neg_top, EReal.coe_sub_bot]
  have hTfin : ∀ ρ lam, (hρ : 0 ≤ ρ) → (h : L ρ ≠ ⊤) →
      T ρ lam = ((-lam * ρ + (L ρ).toReal : ℝ) : EReal) := by
    intro ρ lam hρ h
    simp only [hT]
    rw [← EReal.coe_toReal h (hnb ρ hρ), ← EReal.coe_neg, ← EReal.coe_sub, sub_neg_eq_add, EReal.toReal_coe]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro lam _
    rw [hF]
    refine le_iSup_of_le 0 ?_
    simp only [hT, mul_zero, EReal.coe_zero, zero_sub, neg_neg]
    exact hlb 0 le_rfl
  · intro a _ b _ hab
    rw [hF, hF]
    refine iSup_mono fun ρ => ?_
    rcases lt_or_ge ρ 0 with hρ | hρ
    · rw [hTneg ρ b hρ]; exact bot_le
    · simp only [hT]
      refine EReal.sub_le_sub ?_ le_rfl
      exact_mod_cast (by nlinarith : -b * ρ ≤ -a * ρ)
  · intro a b t ha hb ht0 ht1
    rcases ht0.lt_or_eq with ht0' | ht0'
    swap
    · subst ht0'; simp
    rcases ht1.lt_or_eq with ht1' | ht1'
    swap
    · subst ht1'; simp
    rw [hF ((1 - t) * a + t * b)]
    refine iSup_le fun ρ => ?_
    rcases lt_or_ge ρ 0 with hρ | hρ
    · rw [hTneg ρ _ hρ]; exact bot_le
    have h1t : (0 : EReal) ≤ ((1 - t : ℝ) : EReal) := by exact_mod_cast (by linarith : (0:ℝ) ≤ 1 - t)
    have ht : (0 : EReal) ≤ ((t : ℝ) : EReal) := by exact_mod_cast ht0
    have hle : T ρ ((1 - t) * a + t * b) ≤
        ((1 - t : ℝ) : EReal) * T ρ a + ((t : ℝ) : EReal) * T ρ b := by
      by_cases htop : L ρ = ⊤
      · rw [hTtop ρ _ htop, hTtop ρ _ htop, hTtop ρ _ htop,
          EReal.coe_mul_top_of_pos (by linarith : (0:ℝ) < 1 - t), EReal.coe_mul_top_of_pos ht0',
          EReal.top_add_top]
      · rw [hTfin ρ _ hρ htop, hTfin ρ _ hρ htop, hTfin ρ _ hρ htop, ← EReal.coe_mul,
          ← EReal.coe_mul, ← EReal.coe_add]
        exact_mod_cast le_of_eq (by ring)
    refine hle.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left (by rw [hF]; exact le_iSup (fun ρ => T ρ a) ρ) h1t
    · exact mul_le_mul_of_nonneg_left (by rw [hF]; exact le_iSup (fun ρ => T ρ b) ρ) ht
  · have : F = fun lam => ⨆ ρ, T ρ lam := funext hF
    rw [this]
    refine (lowerSemicontinuous_iSup fun ρ => ?_).lowerSemicontinuousOn _
    rcases lt_or_ge ρ 0 with hρ | hρ
    · have : T ρ = fun _ => ⊥ := funext fun lam => hTneg ρ lam hρ
      rw [this]; exact lowerSemicontinuous_const
    by_cases htop : L ρ = ⊤
    · have : T ρ = fun _ => ⊤ := funext fun lam => hTtop ρ lam htop
      rw [this]; exact lowerSemicontinuous_const
    · have : T ρ = fun lam => ((-lam * ρ + (L ρ).toReal : ℝ) : EReal) :=
        funext fun lam => hTfin ρ lam hρ htop
      rw [this]
      exact (continuous_coe_real_ereal.comp (by fun_prop)).lowerSemicontinuous
