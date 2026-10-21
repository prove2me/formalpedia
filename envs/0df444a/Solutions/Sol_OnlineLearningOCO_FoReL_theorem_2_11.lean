-- Prove2me | solution 1 for OnlineLearningOCO.FoReL.theorem_2_11
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:44:55.888624+00:00
-- url     : https://prove2.me/submissions/51414896-7d2e-4bef-af01-02ffef0530b5

import Mathlib
import Definitions.Def_OnlineLearningOCO_FoReL_regret
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
theorem OLF_23_aux {E : Type*} (S : Set E) (f : ℕ → E → ℝ) (R : E → ℝ) (w : ℕ → E)
    (hw : IsFoReLRun S f R w) (T : ℕ) :
    ∀ u ∈ S, ∑ t ∈ Finset.Icc 1 T, f t (w (t + 1)) + R (w 1) ≤
      ∑ t ∈ Finset.Icc 1 T, f t u + R u := by
  induction T with
  | zero =>
    intro u hu
    obtain ⟨_, hm⟩ := hw 1 le_rfl
    simpa using hm u hu
  | succ T ih =>
    intro u hu
    obtain ⟨hS2, hm2⟩ := hw (T + 2) (by omega)
    have h1 := ih (w (T + 2)) hS2
    have h2 := hm2 u hu
    have hI : Finset.Ico 1 (T + 2) = Finset.Icc 1 (T + 1) := by
      ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hI, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)] at h2
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    linarith

theorem OLF_lemma_2_3 {E : Type*} (S : Set E) (f : ℕ → E → ℝ) (R : E → ℝ) (w : ℕ → E)
    (hw : IsFoReLRun S f R w) (T : ℕ) :
    ∀ u ∈ S,
      ∑ t ∈ Finset.Icc 1 T, (f t (w t) - f t u)
        ≤ R u - R (w 1) + ∑ t ∈ Finset.Icc 1 T, (f t (w t) - f t (w (t + 1))) := by
  intro u hu
  have := OLF_23_aux S f R w hw T u hu
  simp only [Finset.sum_sub_distrib]
  linarith
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
    (hR : StrongConvexOn S σ R) (T : ℕ) (hT : 0 < T)
    (hf : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ S (f t))
    (Lt : ℕ → ℝ)
    (hLip : ∀ t ∈ Finset.Icc 1 T, ∀ u ∈ S, ∀ v ∈ S, |f t u - f t v| ≤ Lt t * ‖u - v‖)
    (L : ℝ) (hL : (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, Lt t ^ 2 ≤ L ^ 2)
    (hw : IsFoReLRun S f R w) :
    ∀ u ∈ S, regret f w T u ≤ R u - sInf (R '' S) + T * L ^ 2 / σ := by
  intro u hu
  have hw1S : w 1 ∈ S := (hw 1 le_rfl).1
  have hmin : R (w 1) = sInf (R '' S) := by
    symm
    apply IsLeast.csInf_eq
    refine ⟨⟨w 1, hw1S, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have := (hw 1 le_rfl).2 v hv
    simpa using this
  have h23 := OLF_lemma_2_3 S f R w hw T u hu
  have h210 : ∀ t ∈ Finset.Icc 1 T, f t (w t) - f t (w (t + 1)) ≤ Lt t ^ 2 / σ := by
    intro t ht
    have ht' := Finset.mem_Icc.1 ht
    have := OLF_lemma_2_10 S σ hσ f R w hR t ht'.1
      (fun i hi => hf i (by simp only [Finset.mem_Icc] at hi ⊢; omega)) (Lt t) (hLip t ht) hw
    exact le_trans this.1 this.2
  have hsum : ∑ t ∈ Finset.Icc 1 T, (f t (w t) - f t (w (t + 1))) ≤ ∑ t ∈ Finset.Icc 1 T, Lt t ^ 2 / σ :=
    Finset.sum_le_sum h210
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hsq : ∑ t ∈ Finset.Icc 1 T, Lt t ^ 2 ≤ T * L ^ 2 := by
    have := hL
    rw [one_div, inv_mul_le_iff₀ hTpos] at this
    exact this
  have hdiv : ∑ t ∈ Finset.Icc 1 T, Lt t ^ 2 / σ ≤ T * L ^ 2 / σ := by
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right hsq hσ.le
  unfold regret
  rw [hmin] at h23
  rw [Finset.sum_sub_distrib] at h23
  linarith
