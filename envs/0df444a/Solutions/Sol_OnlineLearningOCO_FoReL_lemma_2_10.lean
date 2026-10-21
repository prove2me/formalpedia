-- Prove2me | solution 1 for OnlineLearningOCO.FoReL.lemma_2_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:46:42.974602+00:00
-- url     : https://prove2.me/submissions/4bd09d64-58b1-46ee-8258-70b03f2d617c

import Mathlib
import Definitions.Def_OnlineLearningOCO_FoReL_IsFoReLRun
set_option autoImplicit false
open OnlineLearningOCO.FoReL

theorem OLF_strong_min {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (σ : ℝ) (F : E → ℝ) (hF : StrongConvexOn S σ F)
    (w : E) (hwS : w ∈ S) (hwmin : ∀ v ∈ S, F w ≤ F v) :
    ∀ u ∈ S, σ / 2 * ‖u - w‖ ^ 2 ≤ F u - F w := by
  intro u hu
  have key : ∀ t : ℝ, t ∈ Set.Ioo (0:ℝ) 1 →
      (1 - t) * (σ / 2 * ‖u - w‖ ^ 2) ≤ F u - F w := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h1 := hF.2 hwS hu (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    have h2 : F w ≤ F ((1 - t) • w + t • u) :=
      hwmin _ (hF.1 hwS hu (by linarith) ht0.le (by ring))
    have h3 : ‖w - u‖ = ‖u - w‖ := norm_sub_rev _ _
    rw [h3] at h1
    simp only [smul_eq_mul] at h1
    have h4 : t * ((1 - t) * (σ / 2 * ‖u - w‖ ^ 2)) ≤ t * (F u - F w) := by
      nlinarith
    exact le_of_mul_le_mul_left h4 ht0
  have hne : (nhdsWithin (0:ℝ) (Set.Ioo 0 1)).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioo (by norm_num)]
    simp
  have hlim : Filter.Tendsto (fun t : ℝ => (1 - t) * (σ / 2 * ‖u - w‖ ^ 2))
      (nhdsWithin (0:ℝ) (Set.Ioo 0 1)) (nhds ((1 - 0) * (σ / 2 * ‖u - w‖ ^ 2))) :=
    (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
  have := le_of_tendsto hlim (eventually_nhdsWithin_of_forall key)
  simpa using this

theorem OLF_convex_sum {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) (hS : Convex ℝ S)
    (f : ℕ → E → ℝ) (A : Finset ℕ) (hf : ∀ i ∈ A, ConvexOn ℝ S (f i)) :
    ConvexOn ℝ S (fun v => ∑ i ∈ A, f i v) := by
  induction A using Finset.induction_on with
  | empty => simpa using convexOn_const (0:ℝ) hS
  | insert a A ha ih =>
    have h1 := hf a (Finset.mem_insert_self a A)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have := h1.add h2
    have e : (fun v => ∑ i ∈ insert a A, f i v) = f a + fun v => ∑ i ∈ A, f i v := by
      ext v; simp [Finset.sum_insert ha]
    rw [e]; exact this

theorem OLF_strong_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (σ : ℝ) (G R : E → ℝ) (hG : ConvexOn ℝ S G) (hR : StrongConvexOn S σ R) :
    StrongConvexOn S σ (fun v => G v + R v) := by
  have h0 : StrongConvexOn S 0 G := strongConvexOn_zero.2 hG
  have := h0.add hR
  show UniformConvexOn S (fun r : ℝ => σ / 2 * r ^ 2) (G + R)
  have e : (fun r : ℝ => σ / 2 * r ^ 2) = (fun r : ℝ => (0:ℝ) / 2 * r ^ 2) + fun r : ℝ => σ / 2 * r ^ 2 := by
    ext r; simp
  rw [e]; exact this
theorem OLF_stab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (σ : ℝ) (f : ℕ → E → ℝ) (R : E → ℝ) (w : ℕ → E)
    (hR : StrongConvexOn S σ R) (t : ℕ) (ht : 1 ≤ t)
    (hf : ∀ i ∈ Finset.Icc 1 t, ConvexOn ℝ S (f i))
    (hw : IsFoReLRun S f R w) :
    σ * ‖w t - w (t + 1)‖ ^ 2 ≤ f t (w t) - f t (w (t + 1)) := by
  have hS : Convex ℝ S := hR.1
  obtain ⟨hwt, hmt⟩ := hw t ht
  obtain ⟨hwt1, hmt1⟩ := hw (t + 1) (by omega)
  have hIco : Finset.Ico 1 (t + 1) = insert t (Finset.Ico 1 t) := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  have ht_not : t ∉ Finset.Ico 1 t := by simp
  have hsum1 : ∀ v, ∑ i ∈ Finset.Ico 1 (t + 1), f i v = f t v + ∑ i ∈ Finset.Ico 1 t, f i v := by
    intro v; rw [hIco, Finset.sum_insert ht_not]
  -- strong convexity of F_t and F_{t+1}
  have hc1 : ConvexOn ℝ S (fun v => ∑ i ∈ Finset.Ico 1 t, f i v) :=
    OLF_convex_sum S hS f _ (fun i hi => hf i (by
      simp only [Finset.mem_Ico, Finset.mem_Icc] at hi ⊢; omega))
  have hc2 : ConvexOn ℝ S (fun v => ∑ i ∈ Finset.Ico 1 (t + 1), f i v) :=
    OLF_convex_sum S hS f _ (fun i hi => hf i (by
      simp only [Finset.mem_Ico, Finset.mem_Icc] at hi ⊢; omega))
  have hF1 := OLF_strong_add S σ _ R hc1 hR
  have hF2 := OLF_strong_add S σ _ R hc2 hR
  have k1 := OLF_strong_min S σ _ hF1 (w t) hwt hmt (w (t + 1)) hwt1
  have k2 := OLF_strong_min S σ _ hF2 (w (t + 1)) hwt1 hmt1 (w t) hwt
  rw [hsum1, hsum1] at k2
  have h3 : ‖w (t + 1) - w t‖ = ‖w t - w (t + 1)‖ := norm_sub_rev _ _
  rw [h3] at k1
  rw [norm_sub_rev] at k2
  rw [h3] at k2
  nlinarith
theorem OLF_lemma_2_10 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (σ : ℝ) (hσ : 0 < σ) (f : ℕ → E → ℝ) (R : E → ℝ) (w : ℕ → E)
    (hR : StrongConvexOn S σ R) (t : ℕ) (ht : 1 ≤ t)
    (hf : ∀ i ∈ Finset.Icc 1 t, ConvexOn ℝ S (f i))
    (Lt : ℝ) (hLip : ∀ u ∈ S, ∀ v ∈ S, |f t u - f t v| ≤ Lt * ‖u - v‖)
    (hw : IsFoReLRun S f R w) :
    f t (w t) - f t (w (t + 1)) ≤ Lt * ‖w t - w (t + 1)‖ ∧
      Lt * ‖w t - w (t + 1)‖ ≤ Lt ^ 2 / σ := by
  have h27 := OLF_stab S σ f R w hR t ht hf hw
  have hwt : w t ∈ S := (hw t ht).1
  have hwt1 : w (t + 1) ∈ S := (hw (t + 1) (by omega)).1
  have hL := le_trans (le_abs_self _) (hLip _ hwt _ hwt1)
  refine ⟨hL, ?_⟩
  set n := ‖w t - w (t + 1)‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  have h1 : σ * n ^ 2 ≤ Lt * n := le_trans h27 hL
  rcases hn0.eq_or_lt with h | h
  · rw [← h]; simp; positivity
  · have h2 : σ * n ≤ Lt := by nlinarith
    rw [le_div_iff₀ hσ]
    nlinarith [sq_nonneg Lt]

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (σ : ℝ) (hσ : 0 < σ) (f : ℕ → E → ℝ) (R : E → ℝ) (w : ℕ → E)
    (hR : StrongConvexOn S σ R) (t : ℕ) (ht : 1 ≤ t)
    (hf : ∀ i ∈ Finset.Icc 1 t, ConvexOn ℝ S (f i))
    (Lt : ℝ) (hLip : ∀ u ∈ S, ∀ v ∈ S, |f t u - f t v| ≤ Lt * ‖u - v‖)
    (hw : IsFoReLRun S f R w) :
    f t (w t) - f t (w (t + 1)) ≤ Lt * ‖w t - w (t + 1)‖ ∧
      Lt * ‖w t - w (t + 1)‖ ≤ Lt ^ 2 / σ :=
  OLF_lemma_2_10 S σ hσ f R w hR t ht hf Lt hLip hw
