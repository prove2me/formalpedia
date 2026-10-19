-- Prove2me | solution 1 for TikhonovHDD.Weak.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:33:05.675978+00:00
-- url     : https://prove2.me/submissions/5ce285e2-433f-459f-98c2-21f8a1ffe9c1

import Mathlib

set_option autoImplicit false

open Filter Topology Set MeasureTheory

theorem solution (t₀ : ℝ) (ht₀ : 0 < t₀) (F G : ℝ → ℝ)
    (hF : ∀ T : ℝ, t₀ ≤ T → AbsolutelyContinuousOnInterval F t₀ T)
    (hFbdd : BddBelow (F '' Ici t₀))
    (hG : IntegrableOn G (Ici t₀))
    (hFG : ∀ᵐ t ∂(volume.restrict (Ici t₀)), deriv F t ≤ G t) :
    ∃ L : ℝ, Tendsto F atTop (𝓝 L) := by
  obtain ⟨m, hm⟩ := hFbdd
  have hmF : ∀ t, t₀ ≤ t → m ≤ F t := fun t ht => hm ⟨t, ht, rfl⟩
  -- interval integrability of G
  have hGI : ∀ a b, t₀ ≤ a → a ≤ b → IntervalIntegrable G volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hG.mono_set (fun x hx => le_of_lt (lt_of_le_of_lt ha hx.1))
  have hGI' : ∀ b, t₀ ≤ b → IntervalIntegrable G volume t₀ b := fun b hb => hGI t₀ b le_rfl hb
  set Φ : ℝ → ℝ := fun t => ∫ s in t₀..t, G s with hΦ
  set H : ℝ → ℝ := fun t => F t - Φ t with hH
  have hHanti : ∀ a b, t₀ ≤ a → a ≤ b → H b ≤ H a := by
    intro a b ha hab
    have hb : t₀ ≤ b := le_trans ha hab
    have hac : AbsolutelyContinuousOnInterval F a b :=
      (hF b hb).mono (by
        rw [uIcc_of_le hab, uIcc_of_le hb]
        exact Icc_subset_Icc ha le_rfl)
    have h1 : F b - F a = ∫ s in a..b, deriv F s := hac.integral_deriv_eq_sub.symm
    have h2 : Φ b - Φ a = ∫ s in a..b, G s :=
      intervalIntegral.integral_interval_sub_left (hGI' b hb) (hGI' a ha)
    have h3 : (∫ s in a..b, deriv F s) ≤ ∫ s in a..b, G s := by
      apply intervalIntegral.integral_mono_ae_restrict hab hac.intervalIntegrable_deriv
        (hGI a b ha hab)
      exact ae_restrict_of_ae_restrict_of_subset (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr ha)) hFG
    simp only [hH]
    linarith
  -- bound Φ above
  have hGabs : IntegrableOn (fun s => |G s|) (Ioi t₀) :=
    (hG.mono_set Ioi_subset_Ici_self).abs
  set K : ℝ := ∫ s in Ioi t₀, |G s| with hK
  have hΦK : ∀ t, t₀ ≤ t → Φ t ≤ K := by
    intro t ht
    simp only [hΦ]
    rw [intervalIntegral.integral_of_le ht]
    have hGt : IntegrableOn G (Ioc t₀ t) := hG.mono_set (fun x hx => le_of_lt hx.1)
    calc (∫ s in Ioc t₀ t, G s) ≤ ∫ s in Ioc t₀ t, |G s| :=
          setIntegral_mono hGt hGt.abs (fun s => le_abs_self _)
      _ ≤ K := setIntegral_mono_set hGabs
          (Eventually.of_forall (fun s => abs_nonneg _)) (Eventually.of_forall Ioc_subset_Ioi_self)
  -- H' antitone, bounded below
  set H' : ℝ → ℝ := fun t => H (max t t₀) with hH'
  have hH'anti : Antitone H' := by
    intro a b hab
    exact hHanti _ _ (le_max_right _ _) (max_le_max hab le_rfl)
  have hH'bdd : BddBelow (range H') := by
    refine ⟨m - K, ?_⟩
    rintro _ ⟨t, rfl⟩
    have h1 := hmF (max t t₀) (le_max_right _ _)
    have h2 := hΦK (max t t₀) (le_max_right _ _)
    simp only [hH', hH]
    linarith
  have hH'lim := tendsto_atTop_ciInf hH'anti hH'bdd
  -- Φ converges
  have hΦlim : Tendsto Φ atTop (𝓝 (∫ s in Ioi t₀, G s)) :=
    intervalIntegral_tendsto_integral_Ioi t₀ (hG.mono_set Ioi_subset_Ici_self) tendsto_id
  refine ⟨(⨅ i, H' i) + ∫ s in Ioi t₀, G s, ?_⟩
  have := hH'lim.add hΦlim
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop t₀] with t ht
  simp only [hH', hH, max_eq_left ht]
  ring
