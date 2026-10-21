-- Prove2me | solution 1 for OnlineLearningOCO.FoReL.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:44:54.822992+00:00
-- url     : https://prove2.me/submissions/c020221e-a1b7-4bda-bd47-a6b6691f77a4

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

theorem solution {E : Type*} (S : Set E) (f : ℕ → E → ℝ) (R : E → ℝ) (w : ℕ → E)
    (hw : IsFoReLRun S f R w) (T : ℕ) :
    ∀ u ∈ S,
      ∑ t ∈ Finset.Icc 1 T, (f t (w t) - f t u)
        ≤ R u - R (w 1) + ∑ t ∈ Finset.Icc 1 T, (f t (w t) - f t (w (t + 1))) :=
  OLF_lemma_2_3 S f R w hw T
