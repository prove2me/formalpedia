-- Prove2me | solution 1 for OfflineStochMatch.InfinitePatience.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:26:48.363967+00:00
-- url     : https://prove2.me/submissions/5aae5e85-1acc-44b9-8ddf-e3d23fa0cd11

import Mathlib
import Definitions.Def_OfflineStochMatch_InfinitePatience_Setting
set_option autoImplicit false
open OfflineStochMatch.InfinitePatience

lemma rr_pt (aT : ℝ → ℝ) (h1 : ∀ z ∈ Set.Icc (0:ℝ) 1, aT z ∈ Set.Icc (0:ℝ) 1) (h0 : aT 0 = 1)
    (x : ℝ) (hx : x ∈ Set.Ioo (0:ℝ) 1)
    (hc : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun z => Real.log (1 - x * z * aT z)))
    (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    Real.exp (-(x*y)) ≤ 1 - x * aT y * y := by
  rcases hy.1.eq_or_lt with h | hypos
  · subst h; simp
  have hy1 := hy.2
  have hx0 := hx.1
  have hx1 := hx.2
  have hpos : ∀ z ∈ Set.Icc (0:ℝ) 1, 0 < 1 - x * z * aT z := by
    intro z hz
    have h2 := h1 z hz
    have h3 : z * aT z ≤ 1 := by nlinarith [hz.1, hz.2, h2.1, h2.2]
    have h4 : x * (z * aT z) ≤ x * 1 := mul_le_mul_of_nonneg_left h3 hx0.le
    nlinarith
  set g : ℝ → ℝ := fun z => Real.log (1 - x * z * aT z) with hg
  have hg0 : g 0 = 0 := by simp [hg]
  have hgy0 : g y ≤ 0 := by
    have := hpos y hy
    have h5 : 1 - x * y * aT y ≤ 1 := by
      have := (h1 y hy).1
      nlinarith [mul_nonneg (mul_nonneg hx0.le hypos.le) this]
    exact Real.log_nonpos this.le h5
  have hgy : Real.exp (g y) = 1 - x * y * aT y := Real.exp_log (hpos y hy)
  have key : ∀ s, 0 < s → s ≤ y → s * g y ≤ g y + x * y := by
    intro s hs hsy
    have hs1 : s ≤ 1 := hsy.trans hy1
    have hsm : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs.le, hs1⟩
    have hconv := hc.2 (⟨le_refl _, zero_le_one⟩ : (0:ℝ) ∈ Set.Icc (0:ℝ) 1) hy
      (show (0:ℝ) ≤ 1 - s / y by rw [sub_nonneg, div_le_one hypos]; exact hsy)
      (show (0:ℝ) ≤ s / y by positivity) (show (1 - s / y) + s / y = 1 by ring)
    simp only [smul_eq_mul, mul_zero, zero_add] at hconv
    have hbs : s / y * y = s := by field_simp
    rw [hbs] at hconv
    have hconv' : g s ≤ s / y * g y := by
      have : g 0 = 0 := hg0
      simp only [hg] at hconv this ⊢
      rw [this] at hconv
      simpa using hconv
    have hys : y * g s ≤ s * g y := by
      have := mul_le_mul_of_nonneg_left hconv' hypos.le
      calc y * g s ≤ y * (s / y * g y) := this
        _ = s * g y := by field_simp
    have ht : 0 < 1 - x * s := by nlinarith
    have hlt : Real.log (1 - x * s) ≤ g s := by
      apply Real.log_le_log ht
      have := (h1 s hsm).2
      nlinarith [mul_nonneg hx0.le hs.le]
    have hl : (1 - x * s) - 1 ≤ (1 - x * s) * Real.log (1 - x * s) := by
      have := Real.one_sub_inv_le_log_of_pos ht
      have h6 := mul_le_mul_of_nonneg_left this ht.le
      have h7 : (1 - x * s) * (1 - (1 - x * s)⁻¹) = (1 - x * s) - 1 := by field_simp
      linarith
    have h8 : -(x * s) ≤ g s * (1 - x * s) := by
      have := mul_le_mul_of_nonneg_right hlt ht.le
      nlinarith
    have h9 : s * (-(y * x)) ≤ s * (g y * (1 - x * s)) := by
      have := mul_le_mul_of_nonneg_left h8 hypos.le
      nlinarith
    have h10 : -(y * x) ≤ g y * (1 - x * s) := le_of_mul_le_mul_left h9 hs
    have h11 : s * g y ≤ x * s * g y := by nlinarith [mul_nonneg hs.le (sub_nonneg.2 hx1.le), mul_nonneg (mul_nonneg hs.le (sub_nonneg.2 hx1.le)) (neg_nonneg.2 hgy0)]
    nlinarith
  have hfin : -(x * y) ≤ g y := by
    by_contra hneg
    push_neg at hneg
    set c := -(g y + x * y) with hcdef
    set d := -g y with hddef
    have hc0 : 0 < c := by linarith
    have hd0 : 0 < d := by nlinarith [mul_pos hx0 hypos]
    set s := min y (c / (2 * d)) with hsdef
    have hs0 : 0 < s := lt_min hypos (by positivity)
    have hsy : s ≤ y := min_le_left _ _
    have hsd : s ≤ c / (2 * d) := min_le_right _ _
    have := key s hs0 hsy
    have h12 : s * d ≤ c / 2 := by
      calc s * d ≤ c / (2 * d) * d := mul_le_mul_of_nonneg_right hsd hd0.le
        _ = c / 2 := by field_simp
    nlinarith
  calc Real.exp (-(x * y)) ≤ Real.exp (g y) := Real.exp_le_exp.2 hfin
    _ = 1 - x * y * aT y := hgy
    _ = 1 - x * aT y * y := by ring

lemma rr_prod {ι : Type*} (S : Finset ι) (yy : ι → ℝ) (hy : ∀ f ∈ S, 0 ≤ yy f ∧ yy f ≤ 1)
    (aT : ℝ → ℝ) (h1 : ∀ z ∈ Set.Icc (0:ℝ) 1, aT z ∈ Set.Icc (0:ℝ) 1) (h0 : aT 0 = 1)
    (hconv : ∀ x ∈ Set.Ioo (0:ℝ) 1, ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun z => Real.log (1 - x * z * aT z)))
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    Real.exp (-(x * ∑ f ∈ S, yy f)) ≤ ∏ f ∈ S, (1 - x * aT (yy f) * yy f) := by
  have hclosed : IsClosed {x : ℝ | Real.exp (-(x * ∑ f ∈ S, yy f)) ≤ ∏ f ∈ S, (1 - x * aT (yy f) * yy f)} := by
    apply isClosed_le
    · fun_prop
    · fun_prop
  have hsub : Set.Ioo (0:ℝ) 1 ⊆ {x : ℝ | Real.exp (-(x * ∑ f ∈ S, yy f)) ≤ ∏ f ∈ S, (1 - x * aT (yy f) * yy f)} := by
    intro x hx
    simp only [Set.mem_setOf_eq]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro f _; exact (Real.exp_pos _).le
    · intro f hf
      exact rr_pt aT h1 h0 x hx (hconv x hx) (yy f) (hy f hf)
  have := hclosed.closure_subset_iff.2 hsub
  rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at this
  exact this hx

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ) (aT : ℝ → ℝ)
    (haT : IsEffective aT) (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (hy : ∀ f, 0 ≤ y f ∧ y f ≤ 1)
    (e : E) (r : V) (hr : r ∈ G.ends e) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-(x * ∑ f ∈ E1 G p e r, y f))
      ≤ ∏ f ∈ E1 G p e r, (1 - x * aT (p f * y f) * y f) := by
  have h := rr_prod (E1 G p e r) y
    (fun f _ => hy f) aT haT.1 haT.2.1 haT.2.2 x hx
  refine h.trans (le_of_eq ?_)
  apply Finset.prod_congr rfl
  intro f hf
  have : p f = 1 := (Finset.mem_filter.1 hf).2.2
  simp [this]
