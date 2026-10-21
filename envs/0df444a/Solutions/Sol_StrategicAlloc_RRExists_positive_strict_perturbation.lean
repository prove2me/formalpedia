-- Prove2me | solution 1 for StrategicAlloc.RRExists.positive_strict_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:26:35.663799+00:00
-- url     : https://prove2.me/submissions/c1b3b5c2-1d5d-4786-85e2-2d758f9bb220

import Mathlib
import Definitions.Def_StrategicAlloc_RRExists_Setting

set_option autoImplicit false

lemma bundleGap_pos {m : ℕ} (w : Fin m → ℝ) : 0 < StrategicAlloc.RRExists.bundleGap w := by
  unfold StrategicAlloc.RRExists.bundleGap
  simp only
  split_ifs with h
  · have hm := Finset.min'_mem _ h
    rw [Finset.mem_image] at hm
    obtain ⟨p, hp, hpe⟩ := hm
    rw [Finset.mem_filter] at hp
    rw [← hpe]
    exact abs_pos.mpr (sub_ne_zero.mpr hp.2)
  · exact one_pos

lemma goodGap_pos {m : ℕ} (w : Fin m → ℝ) : 0 < StrategicAlloc.RRFair.goodGap w := by
  unfold StrategicAlloc.RRFair.goodGap
  simp only
  split_ifs with h
  · have hm := Finset.min'_mem _ h
    rw [Finset.mem_image] at hm
    obtain ⟨p, hp, hpe⟩ := hm
    rw [Finset.mem_filter] at hp
    rw [← hpe]
    exact abs_pos.mpr (sub_ne_zero.mpr hp.2)
  · exact one_pos

lemma goodGap_le {m : ℕ} (w : Fin m → ℝ) (g h : Fin m) (hne : w g ≠ w h) :
    StrategicAlloc.RRFair.goodGap w ≤ |w g - w h| := by
  unfold StrategicAlloc.RRFair.goodGap
  simp only
  have hmem : |w g - w h| ∈
      ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin m × Fin m => w p.1 ≠ w p.2)).image
    (fun p => |w p.1 - w p.2|) := by
    rw [Finset.mem_image]
    exact ⟨(g, h), by simp [hne], rfl⟩
  rw [dif_pos ⟨_, hmem⟩]
  exact Finset.min'_le _ _ hmem

theorem solution {m : ℕ} (w : Fin m → ℝ) (hw : ∀ g, 0 ≤ w g) :
    ∃ w' : Fin m → ℝ, (∀ g, 0 < w' g) ∧ Function.Injective w' ∧
      (∀ g h, w g < w h → w' g < w' h) ∧
      ∀ T : Finset (Fin m), ∑ g ∈ T, w g ≤ ∑ g ∈ T, w' g ∧
        ∑ g ∈ T, w' g ≤ ∑ g ∈ T, w g + 2 * StrategicAlloc.RRFair.goodGap w / 3 ∧
        ∑ g ∈ T, w' g ≤ ∑ g ∈ T, w g + 2 * StrategicAlloc.RRExists.bundleGap w / 3 := by
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = min (StrategicAlloc.RRFair.goodGap w) (StrategicAlloc.RRExists.bundleGap w) := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; exact lt_min (goodGap_pos w) (bundleGap_pos w)
  have he1 : e ≤ StrategicAlloc.RRFair.goodGap w := by rw [he]; exact min_le_left _ _
  have he2 : e ≤ StrategicAlloc.RRExists.bundleGap w := by rw [he]; exact min_le_right _ _
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = e / (2 * ((m : ℝ) + 1) ^ 2) := ⟨_, rfl⟩
  have hm1 : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 := by positivity
  have hη0 : 0 < η := by rw [hη]; positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin m → ℝ, δ = fun g => η * ((g.val : ℝ) + 1) := ⟨_, rfl⟩
  have hδpos : ∀ g, 0 < δ g := fun g => by rw [hδ]; exact mul_pos hη0 (by positivity)
  have hδle : ∀ g, δ g ≤ η * m := fun g => by
    simp only [hδ]
    have : ((g.val : ℝ) + 1) ≤ m := by
      have := g.isLt
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_left this hη0.le
  have hηm : η * m < e := by
    have h1 : η * m ≤ η * ((m : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left (by linarith) hη0.le
    have h2 : η * ((m : ℝ) + 1) * ((m : ℝ) + 1) = e / 2 := by
      simp only [hη]; field_simp
    have h3 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have : (0:ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have h4 : η * ((m : ℝ) + 1) ≤ e / 2 := by nlinarith [mul_pos hη0 (by linarith : (0:ℝ) < (m:ℝ) + 1)]
    linarith
  have htot : ∑ g, δ g ≤ e / 2 := by
    calc ∑ g, δ g ≤ ∑ _g : Fin m, η * m := Finset.sum_le_sum (fun g _ => hδle g)
      _ = m * (η * m) := by simp
      _ ≤ e / 2 := by
        have h2 : η * ((m : ℝ) + 1) * ((m : ℝ) + 1) = e / 2 := by
          simp only [hη]; field_simp
        have h0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith [mul_nonneg h0 hη0.le, mul_nonneg (mul_nonneg h0 hη0.le) h0]
  have hord : ∀ g h, w g < w h → w g + δ g < w h + δ h := by
    intro g h hgh
    have := goodGap_le w g h hgh.ne
    rw [abs_of_neg (by linarith)] at this
    have := hδle g
    have := hδpos h
    linarith
  refine ⟨fun g => w g + δ g, fun g => by have := hw g; have := hδpos g; linarith, ?_, ?_, ?_⟩
  · intro g h hgh
    simp only at hgh
    by_contra hne
    rcases lt_trichotomy (w g) (w h) with h1 | h1 | h1
    · have := hord g h h1; linarith
    · have : δ g = δ h := by linarith
      apply hne
      simp only [hδ] at this
      have := mul_left_cancel₀ hη0.ne' this
      apply Fin.ext
      exact_mod_cast (by linarith : (g.val : ℝ) = h.val)
    · have := hord h g h1; linarith
  · intro g h hgh
    exact hord g h hgh
  · intro T
    have hs : ∑ g ∈ T, (w g + δ g) = ∑ g ∈ T, w g + ∑ g ∈ T, δ g := Finset.sum_add_distrib
    have h0 : 0 ≤ ∑ g ∈ T, δ g := Finset.sum_nonneg (fun g _ => (hδpos g).le)
    have h1 : ∑ g ∈ T, δ g ≤ ∑ g, δ g :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun g _ _ => (hδpos g).le)
    refine ⟨by linarith, by linarith, by linarith⟩
