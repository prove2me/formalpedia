-- Prove2me | solution 1 for PolicyGradTheory.ProjGA.beck_projected_gradient_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:54:38.206454+00:00
-- url     : https://prove2.me/submissions/0f0c4b2f-ae70-4253-9fe6-45f76448c6d8

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_Projection

set_option autoImplicit false

open PolicyGradTheory.ProjGA in
theorem e46d63d1_vi {ι : Type*} [Fintype ι] (C : Set (EuclideanSpace ℝ ι)) (hCcv : Convex ℝ C)
    (Proj : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (hProj : IsProjOnto C Proj) (z : EuclideanSpace ℝ ι) :
    ∀ w ∈ C, inner ℝ (z - Proj z) (w - Proj z) ≤ 0 := by
  have hp := (hProj z).1
  have hmin := (hProj z).2
  have hne : Nonempty C := ⟨⟨Proj z, hp⟩⟩
  have hbdd : BddBelow (Set.range fun w : C => ‖z - (w : EuclideanSpace ℝ ι)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have hinf : ‖z - Proj z‖ = ⨅ w : C, ‖z - (w : EuclideanSpace ℝ ι)‖ := by
    apply le_antisymm
    · exact le_ciInf (fun w : C => hmin w.1 w.2)
    · exact ciInf_le hbdd (⟨Proj z, hp⟩ : C)
  exact (norm_eq_iInf_iff_real_inner_le_zero hCcv hp).1 hinf

theorem e46d63d1_descent {ι : Type*} [Fintype ι] (C : Set (EuclideanSpace ℝ ι))
    (hCcv : Convex ℝ C) (f : EuclideanSpace ℝ ι → ℝ) (β : ℝ) (hβ : 0 < β)
    (hdiff : ∀ x ∈ C, DifferentiableAt ℝ f x)
    (hsmooth : ∀ x ∈ C, ∀ y ∈ C, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖)
    (a b : EuclideanSpace ℝ ι) (ha : a ∈ C) (hb : b ∈ C) :
    f b ≤ f a + inner ℝ (gradient f a) (b - a) + β / 2 * ‖b - a‖ ^ 2 := by
  set v := b - a with hv
  let p : ℝ → EuclideanSpace ℝ ι := fun s => a + s • v
  have hpC : ∀ s ∈ Set.Icc (0:ℝ) 1, p s ∈ C := fun s hs => hCcv.add_smul_sub_mem ha hb hs
  let g : ℝ → ℝ := fun s => f (p s) - f a - s * inner ℝ (gradient f a) v - β / 2 * s ^ 2 * ‖v‖ ^ 2
  have hderiv : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivAt g
      (inner ℝ (gradient f (p s)) v - inner ℝ (gradient f a) v - β * s * ‖v‖ ^ 2) s := by
    intro s hs
    have hpd : HasDerivAt p v s := by
      have := ((hasDerivAt_id s).smul_const v).const_add a
      simpa [p] using this
    have hfg : HasFDerivAt f (InnerProductSpace.toDual ℝ _ (gradient f (p s))) (p s) :=
      hasGradientAt_iff_hasFDerivAt.mp (hdiff _ (hpC s hs)).hasGradientAt
    have h1 := hfg.comp_hasDerivAt s hpd
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (gradient f a) v) (inner ℝ (gradient f a) v) s := by
      simpa using (hasDerivAt_id s).mul_const (inner ℝ (gradient f a) v)
    have h3 : HasDerivAt (fun s : ℝ => β / 2 * s ^ 2 * ‖v‖ ^ 2) (β * s * ‖v‖ ^ 2) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (β / 2)).mul_const (‖v‖ ^ 2)
      exact this.congr_deriv (by rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
    have h1' : HasDerivAt (fun s => f (p s)) (inner ℝ (gradient f (p s)) v) s := by
      simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using h1
    exact ((h1'.sub_const (f a)).sub h2).sub h3
  have hnonpos : ∀ s ∈ Set.Icc (0:ℝ) 1,
      inner ℝ (gradient f (p s)) v - inner ℝ (gradient f a) v - β * s * ‖v‖ ^ 2 ≤ 0 := by
    intro s hs
    have hle := hsmooth (p s) (hpC s hs) a ha
    have hps : p s - a = s • v := by simp [p]
    rw [hps, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1] at hle
    have hcs := real_inner_le_norm (gradient f (p s) - gradient f a) v
    rw [inner_sub_left] at hcs
    have : ‖gradient f (p s) - gradient f a‖ * ‖v‖ ≤ β * (s * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    nlinarith
  have hanti : AntitoneOn g (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · intro s hs; exact (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hderiv s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hderiv s (interior_subset hs)).deriv]
      exact hnonpos s (interior_subset hs)
  have h01 := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  have hp0 : p 0 = a := by simp [p]
  have hp1 : p 1 = b := by simp [p, v]
  simp only [g, hp0, hp1] at h01
  nlinarith

open PolicyGradTheory.ProjGA in
theorem solution {ι : Type*} [Fintype ι]
    (C : Set (EuclideanSpace ℝ ι)) (hCne : C.Nonempty) (hCcl : IsClosed C) (hCcv : Convex ℝ C)
    (f : EuclideanSpace ℝ ι → ℝ) (β : ℝ) (hβ : 0 < β)
    (hdiff : ∀ x ∈ C, DifferentiableAt ℝ f x)
    (hsmooth : ∀ x ∈ C, ∀ y ∈ C, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖)
    (xstar : EuclideanSpace ℝ ι) (hxstar : xstar ∈ C) (hmin : ∀ y ∈ C, f xstar ≤ f y)
    (Proj : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (hProj : IsProjOnto C Proj)
    (x : ℕ → EuclideanSpace ℝ ι) (hx0 : x 0 ∈ C)
    (hrun : ∀ t : ℕ, x (t + 1) = Proj (x t - (1 / β) • gradient f (x t))) :
    ∀ T : ℕ, 0 < T → ∃ t < T,
      ‖β • (x t - Proj (x t - (1 / β) • gradient f (x t)))‖ ≤
        Real.sqrt (2 * β * (f (x 0) - f xstar)) / Real.sqrt (T : ℝ) := by
  have hxC : ∀ t, x t ∈ C := by
    intro t
    induction t with
    | zero => exact hx0
    | succ n _ => rw [hrun n]; exact (hProj _).1
  -- sufficient decrease
  have hdec : ∀ t, β / 2 * ‖x t - x (t + 1)‖ ^ 2 ≤ f (x t) - f (x (t + 1)) := by
    intro t
    set gr := gradient f (x t)
    have hvi := e46d63d1_vi C hCcv Proj hProj (x t - (1 / β) • gr) (x t) (hxC t)
    rw [← hrun t] at hvi
    have hds := e46d63d1_descent C hCcv f β hβ hdiff hsmooth (x t) (x (t + 1)) (hxC t)
      (hxC (t + 1))
    have e1 : x t - (1 / β) • gr - x (t + 1) = (x t - x (t + 1)) - (1 / β) • gr := by abel
    rw [e1, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_smul_left] at hvi
    have e2 : x (t + 1) - x t = -(x t - x (t + 1)) := by abel
    rw [e2, inner_neg_right, norm_neg] at hds
    have e3 : inner ℝ gr (x t - x (t + 1)) = inner ℝ (x t - x (t + 1)) gr := real_inner_comm _ _
    rw [e3] at hds hvi
    have hb1 : β * (1 / β) = 1 := by field_simp
    have : ‖x t - x (t + 1)‖ ^ 2 * β ≤ inner ℝ (x t - x (t + 1)) gr := by
      have := mul_le_mul_of_nonneg_left (by linarith : ‖x t - x (t + 1)‖ ^ 2 ≤
        1 / β * inner ℝ (x t - x (t + 1)) gr) hβ.le
      rw [← mul_assoc, hb1, one_mul] at this
      linarith
    nlinarith
  intro T hT
  -- telescoping
  have htel : ∀ n, ∑ t ∈ Finset.range n, β / 2 * ‖x t - x (t + 1)‖ ^ 2 ≤ f (x 0) - f (x n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ]; linarith [hdec n]
  obtain ⟨t, htT, htmin⟩ := Finset.exists_min_image (Finset.range T)
    (fun t => ‖x t - x (t + 1)‖) ⟨0, Finset.mem_range.2 hT⟩
  refine ⟨t, Finset.mem_range.1 htT, ?_⟩
  rw [← hrun t, norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
  set d := ‖x t - x (t + 1)‖ with hd
  have hsum : (T : ℝ) * (β / 2 * d ^ 2) ≤ f (x 0) - f xstar := by
    have h1 : ∑ s ∈ Finset.range T, β / 2 * d ^ 2 ≤
        ∑ s ∈ Finset.range T, β / 2 * ‖x s - x (s + 1)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      have := htmin s hs
      have hd0 : 0 ≤ d := norm_nonneg _
      have : d ^ 2 ≤ ‖x s - x (s + 1)‖ ^ 2 := by
        exact pow_le_pow_left₀ hd0 this 2
      nlinarith
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    linarith [htel T, hmin (x T) (hxC T)]
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  rw [le_div_iff₀ (Real.sqrt_pos.2 hTpos)]
  have hd0 : 0 ≤ d := norm_nonneg _
  have heq : β * d * Real.sqrt T = Real.sqrt ((β * d) ^ 2 * T) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [heq]
  apply Real.sqrt_le_sqrt
  nlinarith
