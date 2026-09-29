-- Prove2me | solution 1 for SYZ.prop4_variation_of_induced_metric
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-24T12:24:19.589828+00:00
-- url     : https://prove2.me/submissions/325f0fd0-c9da-41db-8706-19d3ad2e4b22

import Definitions.Def_syz_flat_model

set_option autoImplicit false

open SYZ
open scoped ContDiff

variable {n : ℕ}

-- Stage 1: infrastructure. Joint map J p = F p.1 p.2.

-- D (F s) i x as joint fderiv (prior worker's test3, kept)
lemma D_eq_fderiv_joint {F : ℝ → Dom n → Amb n}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    {s : ℝ} {x : Dom n} {i : Fin n} :
    D (F s) i x
      = (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2) (s, x)) (0, basis i) := by
  have h1 : (F s) = (fun p : ℝ × Dom n => F p.1 p.2) ∘ (fun y : Dom n => (s, y)) := rfl
  have h2 : HasFDerivAt (fun y : Dom n => (s, y))
      (ContinuousLinearMap.inr ℝ ℝ (Dom n)) x := by
    have hbase := (ContinuousLinearMap.inr ℝ ℝ (Dom n)).hasFDerivAt (x := x)
    have heq : (fun y : Dom n => (s, y))
        = (fun y => (s, (0 : Dom n)) + (ContinuousLinearMap.inr ℝ ℝ (Dom n)) y) := by
      funext y; simp [ContinuousLinearMap.inr_apply]
    rw [heq]
    simpa using hbase.const_add (s, (0 : Dom n))
  have h3 : HasFDerivAt ((fun p : ℝ × Dom n => F p.1 p.2) ∘ (fun y : Dom n => (s, y)))
      ((fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2) (s, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Dom n))) x :=
    (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x h2
  unfold D
  rw [h1, h3.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

-- fderiv of a C^∞ map is differentiable (via contDiff_infty_iff_fderiv)
lemma hasFDerivAt_fderiv_of_contDiff_infty {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : E → F} (hJ : ContDiff ℝ (⊤ : ℕ∞) J) (p : E) :
    HasFDerivAt (fderiv ℝ J) (fderiv ℝ (fderiv ℝ J) p) p :=
  ((contDiff_infty_iff_fderiv.mp hJ).2.differentiable (by simp)).differentiableAt.hasFDerivAt

-- (2:ℕ∞ω) ≤ ∞
lemma two_le_infty : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
  have h2 : (2 : ℕ∞ω) = ((((2 : ℕ∞)) : ℕ∞ω)) := by simp
  rw [h2]
  exact WithTop.coe_le_coe.mpr le_top

-- Clairaut for the joint map
lemma symmJ {F : ℝ → Dom n → Amb n}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (x : Dom n) :
    IsSymmSndFDerivAt ℝ (fun p : ℝ × Dom n => F p.1 p.2) (t, x) := by
  apply (hF.contDiffAt).isSymmSndFDerivAt
  rw [minSmoothness_of_isRCLikeNormedField]
  exact two_le_infty

-- (starRingEnd ℂ) (I * (c:ℂ)) = -(I * (c:ℂ)) for real c
lemma star_I_mul_ofReal (c : ℝ) :
    (starRingEnd ℂ) (Complex.I * (c : ℂ)) = -(Complex.I * (c : ℂ)) := by
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

-- g(I * (w:ℂ) • u, v) = w * ω(u,v), w real
lemma gAmb_Iw_left (c : ℝ) (u v : Amb n) :
    gAmb ((Complex.I * (c : ℂ)) • u) v = c * kForm u v := by
  unfold gAmb kForm
  rw [inner_smul_left, star_I_mul_ofReal]
  have key : ((-(Complex.I * (c : ℂ))) * inner ℂ u v).re
      = c * (inner ℂ u v).im := by
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  exact key

-- g(u, I * (w:ℂ) • v) = -(w * ω(u,v)), w real
lemma gAmb_Iw_right (c : ℝ) (u v : Amb n) :
    gAmb u ((Complex.I * (c : ℂ)) • v) = -(c * kForm u v) := by
  unfold gAmb kForm
  rw [inner_smul_right]
  have key : ((Complex.I * (c : ℂ)) * inner ℂ u v).re
      = -(c * (inner ℂ u v).im) := by
    simp only [Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [key]

-- the s-curve and y-curve into the joint space
lemma hasFDerivAt_s_curve (t : ℝ) (x : Dom n) :
    HasFDerivAt (fun s : ℝ => (s, x)) (ContinuousLinearMap.inl ℝ ℝ (Dom n)) t := by
  have hbase := (ContinuousLinearMap.inl ℝ ℝ (Dom n)).hasFDerivAt (x := t)
  have heq : (fun s : ℝ => (s, x))
      = (fun s => ((0 : ℝ), x) + (ContinuousLinearMap.inl ℝ ℝ (Dom n)) s) := by
    funext s; simp [ContinuousLinearMap.inl_apply]
  rw [heq]
  simpa using hbase.const_add ((0 : ℝ), x)

lemma hasFDerivAt_y_curve (t : ℝ) (x : Dom n) :
    HasFDerivAt (fun y : Dom n => (t, y)) (ContinuousLinearMap.inr ℝ ℝ (Dom n)) x := by
  have hbase := (ContinuousLinearMap.inr ℝ ℝ (Dom n)).hasFDerivAt (x := x)
  have heq : (fun y : Dom n => (t, y))
      = (fun y => (t, (0 : Dom n)) + (ContinuousLinearMap.inr ℝ ℝ (Dom n)) y) := by
    funext y; simp [ContinuousLinearMap.inr_apply]
  rw [heq]
  simpa using hbase.const_add (t, (0 : Dom n))
-- Stage 2: mixed partials.

-- HasFDerivAt of p ↦ (fderiv ℝ J p) v₀
lemma hasFDerivAt_eval_fderiv {F : ℝ → Dom n → Amb n}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (x : Dom n) (v₀ : ℝ × Dom n) :
    HasFDerivAt (fun p : ℝ × Dom n => (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2) p) v₀)
      ((fderiv ℝ (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2)) (t, x)).flip v₀) (t, x) := by
  have hc := hasFDerivAt_fderiv_of_contDiff_infty hF (t, x)
  have hu : HasFDerivAt (fun _ : ℝ × Dom n => v₀)
      (0 : (ℝ × Dom n) →L[ℝ] (ℝ × Dom n)) (t, x) :=
    hasFDerivAt_const v₀ (t, x)
  have h := hc.clm_apply hu
  simpa using h

-- s-derivative of s ↦ D (F s) i x, valued as the iterated fderiv
lemma hasFDerivAt_s_mixed {F : ℝ → Dom n → Amb n}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (x : Dom n) (i : Fin n) :
    HasDerivAt (fun s => D (F s) i x)
      ((fderiv ℝ (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2)) (t, x)) (1, 0) (0, basis i)) t := by
  have e1 := hasFDerivAt_eval_fderiv hF t x (0, basis i)
  have e2 := hasFDerivAt_s_curve t x
  have e3 := e1.comp t e2
  have efun : (fun s : ℝ => D (F s) i x)
      = (fun p : ℝ × Dom n => (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2) p) (0, basis i))
        ∘ (fun s : ℝ => (s, x)) := by
    funext s
    simp only [Function.comp_apply]
    exact D_eq_fderiv_joint hF
  rw [efun]
  have hderiv := e3.hasDerivAt
  have hval : (((fderiv ℝ (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2)) (t, x)).flip
      (0, basis i)).comp (ContinuousLinearMap.inl ℝ ℝ (Dom n))) 1
      = (fderiv ℝ (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2)) (t, x)) (1, 0) (0, basis i) := by
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.flip_apply]
  rw [hval] at hderiv
  exact hderiv

-- velocity as joint fderiv in the (1,0) direction
lemma vel_eq {F : ℝ → Dom n → Amb n}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (y : Dom n) :
    deriv (fun r => F r y) t
      = (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2) (t, y)) (1, 0) := by
  have hJ : HasFDerivAt (fun p : ℝ × Dom n => F p.1 p.2)
      (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2) (t, y)) (t, y) :=
    (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hc := hJ.comp t (hasFDerivAt_s_curve t y)
  have hfun : (fun r : ℝ => F r y)
      = (fun p : ℝ × Dom n => F p.1 p.2) ∘ (fun r : ℝ => (r, y)) := rfl
  have hderiv := (hasFDerivAt_iff_hasDerivAt.mp hc).deriv
  rw [hfun, hderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

-- HasFDerivAt of the velocity field V y = deriv (fun r => F r y) t
lemma hasFDerivAt_vel {F : ℝ → Dom n → Amb n}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (x : Dom n) :
    HasFDerivAt (fun y => deriv (fun r => F r y) t)
      (((fderiv ℝ (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2)) (t, x)).flip (1, 0)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Dom n))) x := by
  have e1 := hasFDerivAt_eval_fderiv hF t x (1, 0)
  have e2 := hasFDerivAt_y_curve t x
  have e3 := e1.comp x e2
  have efun : (fun y : Dom n => deriv (fun r => F r y) t)
      = (fun p : ℝ × Dom n => (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2) p) (1, 0))
        ∘ (fun y : Dom n => (t, y)) := by
    funext y
    simp only [Function.comp_apply]
    exact vel_eq hF t y
  rw [efun]
  exact e3

-- the commutation: ∂_t ∂_i = ∂_i ∂_t
lemma hasDerivAt_D_comm {F : ℝ → Dom n → Amb n}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (x : Dom n) (i : Fin n) :
    HasDerivAt (fun s => D (F s) i x)
      (D (fun y => deriv (fun r => F r y) t) i x) t := by
  have hs := hasFDerivAt_s_mixed hF t x i
  have hcl := (symmJ hF t x).eq (1, 0) (0, basis i)
  have hv := hasFDerivAt_vel hF t x
  have hD : D (fun y => deriv (fun r => F r y) t) i x
      = (fderiv ℝ (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2)) (t, x)) (0, basis i) (1, 0) := by
    unfold D
    rw [hv.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.flip_apply]
  rw [hD, ← hcl]
  exact hs

-- Stage 3: x-product rule, Lagrangian vanishing, term computations, assembly

-- 1D gAmb product rule (from test2)
lemma hasDerivAt_gAmb_comp {n : ℕ} {A B : ℝ → Amb n} {a' b' : Amb n} {t : ℝ}
    (hA : HasDerivAt A a' t) (hB : HasDerivAt B b' t) :
    HasDerivAt (fun s => gAmb (A s) (B s)) (gAmb a' (B t) + gAmb (A t) b') t := by
  have h := HasDerivAt.inner ℂ hA hB
  have h2 := Complex.reCLM.hasFDerivAt.comp t h.hasFDerivAt
  have h3 := h2.hasDerivAt
  have hder : ((Complex.reCLM ∘SL ContinuousLinearMap.toSpanSingleton ℝ
      (inner ℂ (A t) b' + inner ℂ a' (B t))) 1)
      = gAmb a' (B t) + gAmb (A t) b' := by
    simp [gAmb, Complex.add_re, add_comm]
  have hfun : (⇑Complex.reCLM ∘ fun s => inner ℂ (A s) (B s))
      = (fun s => gAmb (A s) (B s)) := rfl
  rw [hfun, hder] at h3
  exact h3

-- kForm antisymmetry
lemma kForm_antisymm {n : ℕ} (u v : Amb n) : kForm u v = -kForm v u := by
  unfold kForm
  exact inner_im_symm (𝕜 := ℂ) u v

-- gAmb symmetry
lemma gAmb_symm {n : ℕ} (u v : Amb n) : gAmb u v = gAmb v u := by
  unfold gAmb
  exact inner_re_symm (𝕜 := ℂ) u v

-- gAmb through finite sums
lemma gAmb_sum_left {n : ℕ} (a : Fin n → Amb n) (v : Amb n) :
    gAmb (∑ k, a k) v = ∑ k, gAmb (a k) v := by
  unfold gAmb
  rw [sum_inner]
  simp

lemma gAmb_sum_right {n : ℕ} (u : Amb n) (a : Fin n → Amb n) :
    gAmb u (∑ k, a k) = ∑ k, gAmb u (a k) := by
  unfold gAmb
  rw [inner_sum]
  simp

-- Lagrangian vanishing: gAmb (velocity, ∂_j F) = 0 pointwise
lemma lag_zero {n : ℕ} {F : ℝ → Dom n → Amb n} {w : ℝ → Dom n → Fin n → ℝ}
    (hLag : ∀ s y, IsLagrangianAt (F s) y)
    (hflow : ∀ s y, deriv (fun r => F r y) s
      = ∑ k, (Complex.I * (w s y k : ℂ)) • D (F s) k y)
    (t : ℝ) (j : Fin n) (y : Dom n) :
    gAmb (deriv (fun r => F r y) t) (D (F t) j y) = 0 := by
  rw [hflow t y, gAmb_sum_left]
  apply Finset.sum_eq_zero
  intro k _
  rw [gAmb_Iw_left]
  have h0 : kForm (D (F t) k y) (D (F t) j y) = 0 := hLag t y k j
  rw [h0, mul_zero]

-- fderiv of an identically-zero function is zero
lemma fderiv_zero_of_forall_zero {n : ℕ} {L : Dom n → ℝ}
    (hL : ∀ y, L y = 0) (x : Dom n) (d : Dom n) :
    fderiv ℝ L x d = 0 := by
  have heq : L = fun _ => 0 := funext hL
  rw [heq]
  simp

-- fderiv product rule for gAmb, CLM form
lemma hasFDerivAt_gAmb {n : ℕ} {V W : Dom n → Amb n} {V' W' : Dom n →L[ℝ] Amb n}
    {x : Dom n} (hV : HasFDerivAt V V' x) (hW : HasFDerivAt W W' x) (d : Dom n) :
    fderiv ℝ (fun y => gAmb (V y) (W y)) x d
      = gAmb (V' d) (W x) + gAmb (V x) (W' d) := by
  have h1 := HasFDerivAt.inner ℂ hV hW
  have h2 := Complex.reCLM.hasFDerivAt.comp x h1
  have hfun : (fun y => gAmb (V y) (W y))
      = Complex.reCLM ∘ (fun t => inner ℂ (V t) (W t)) := rfl
  rw [hfun, h2.fderiv]
  have hred : (Complex.reCLM.comp ((fderivInnerCLM ℂ (V x, W x)).comp (V'.prod W'))) d
      = gAmb (V' d) (W x) + gAmb (V x) (W' d) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, fderivInnerCLM_apply]
    show Complex.reCLM (inner ℂ (V x) (W' d) + inner ℂ (V' d) (W x))
      = gAmb (V' d) (W x) + gAmb (V x) (W' d)
    simp [gAmb, Complex.add_re, add_comm]
  exact hred

-- fderiv product rule for gAmb, D form
lemma hasFDerivAt_gAmb_D {n : ℕ} {V W : Dom n → Amb n} {V' W' : Dom n →L[ℝ] Amb n}
    {x : Dom n} (hV : HasFDerivAt V V' x) (hW : HasFDerivAt W W' x) (i : Fin n) :
    fderiv ℝ (fun y => gAmb (V y) (W y)) x (basis i)
      = gAmb (D V i x) (W x) + gAmb (V x) (D W i x) := by
  have h := hasFDerivAt_gAmb hV hW (basis i)
  rw [← hV.fderiv, ← hW.fderiv] at h
  show (fderiv ℝ (fun y => gAmb (V y) (W y)) x) (basis i)
      = gAmb ((fderiv ℝ V x) (basis i)) (W x) + gAmb (V x) ((fderiv ℝ W x) (basis i))
  exact h

-- HasFDerivAt for the spatial frame field y ↦ D (F t) j y
lemma hasFDerivAt_W {n : ℕ} {F : ℝ → Dom n → Amb n}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (x : Dom n) (j : Fin n) :
    HasFDerivAt (fun y => D (F t) j y)
      (((fderiv ℝ (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2)) (t, x)).flip
        (0, basis j)).comp (ContinuousLinearMap.inr ℝ ℝ (Dom n))) x := by
  have e1 := hasFDerivAt_eval_fderiv hF t x (0, basis j)
  have e2 := hasFDerivAt_y_curve t x
  have e3 := e1.comp x e2
  have efun : (fun y : Dom n => D (F t) j y)
      = (fun p : ℝ × Dom n => (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2) p) (0, basis j))
        ∘ (fun y : Dom n => (t, y)) := by
    funext y
    simp only [Function.comp_apply]
    exact D_eq_fderiv_joint hF
  rw [efun]
  exact e3

-- spatial Clairaut: D_i D_j = D_j D_i in the x-variable
lemma D_comm_x {n : ℕ} {F : ℝ → Dom n → Amb n}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (x : Dom n) (i j : Fin n) :
    D (fun y => D (F t) i y) j x = D (D (F t) j) i x := by
  have e1 := hasFDerivAt_W hF t x i
  have e2 := hasFDerivAt_W hF t x j
  have hL : D (fun y => D (F t) i y) j x
      = (fderiv ℝ (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2)) (t, x))
        (0, basis j) (0, basis i) := by
    have h2 : fderiv ℝ (fun y => D (F t) i y) x (basis j)
        = (fderiv ℝ (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2)) (t, x))
          (0, basis j) (0, basis i) := by
      rw [e1.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
        ContinuousLinearMap.flip_apply]
    exact h2
  have hR : D (D (F t) j) i x
      = (fderiv ℝ (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2)) (t, x))
        (0, basis i) (0, basis j) := by
    have h2 : fderiv ℝ (fun y => D (F t) j y) x (basis i)
        = (fderiv ℝ (fderiv ℝ (fun p : ℝ × Dom n => F p.1 p.2)) (t, x))
          (0, basis i) (0, basis j) := by
      rw [e2.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
        ContinuousLinearMap.flip_apply]
    exact h2
  rw [hL, hR]
  exact (symmJ hF t x) (0, basis j) (0, basis i)

-- Term 1: g(D_i V, U_j) = ∑ w^k h_ijk
lemma term1 {n : ℕ} {F : ℝ → Dom n → Amb n} {w : ℝ → Dom n → Fin n → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (hLag : ∀ s y, IsLagrangianAt (F s) y)
    (hflow : ∀ s y, deriv (fun r => F r y) s
      = ∑ k, (Complex.I * (w s y k : ℂ)) • D (F s) k y)
    (t : ℝ) (x : Dom n) (i j : Fin n) :
    gAmb (D (fun y => deriv (fun r => F r y) t) i x) (D (F t) j x)
      = ∑ k, w t x k * hTen (F t) i j k x := by
  have hV := hasFDerivAt_vel hF t x
  have hW := hasFDerivAt_W hF t x j
  have hzero : ∀ y : Dom n, gAmb (deriv (fun r => F r y) t) (D (F t) j y) = 0 :=
    fun y => lag_zero hLag hflow t j y
  have hfd0 : fderiv ℝ (fun y : Dom n => gAmb (deriv (fun r => F r y) t) (D (F t) j y))
      x (basis i) = 0 :=
    fderiv_zero_of_forall_zero hzero x (basis i)
  rw [hasFDerivAt_gAmb_D hV hW i] at hfd0
  have hfd : gAmb (D (fun y => deriv (fun r => F r y) t) i x) (D (F t) j x)
      + gAmb (deriv (fun r => F r x) t) (D (fun y => D (F t) j y) i x) = 0 := hfd0
  have hanti : ∀ k : Fin n, kForm (D (F t) k x) (D (fun y => D (F t) j y) i x)
      = -hTen (F t) i j k x := by
    intro k
    have h := kForm_antisymm (D (F t) k x) (D (fun y => D (F t) j y) i x)
    unfold hTen
    exact h
  have hcomp : gAmb (deriv (fun r => F r x) t) (D (fun y => D (F t) j y) i x)
      = -(∑ k, w t x k * hTen (F t) i j k x) := by
    rw [hflow t x, gAmb_sum_left, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [gAmb_Iw_left, hanti k]
    ring
  linarith [hfd, hcomp]

-- Term 2: g(U_i, D_j V) = ∑ w^k h_ijk
lemma term2 {n : ℕ} {F : ℝ → Dom n → Amb n} {w : ℝ → Dom n → Fin n → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (hLag : ∀ s y, IsLagrangianAt (F s) y)
    (hflow : ∀ s y, deriv (fun r => F r y) s
      = ∑ k, (Complex.I * (w s y k : ℂ)) • D (F s) k y)
    (t : ℝ) (x : Dom n) (i j : Fin n) :
    gAmb (D (F t) i x) (D (fun y => deriv (fun r => F r y) t) j x)
      = ∑ k, w t x k * hTen (F t) i j k x := by
  have hW := hasFDerivAt_W hF t x i
  have hV := hasFDerivAt_vel hF t x
  have hzero : ∀ y : Dom n, gAmb (D (F t) i y) (deriv (fun r => F r y) t) = 0 := by
    intro y
    rw [gAmb_symm]
    exact lag_zero hLag hflow t i y
  have hfd0 : fderiv ℝ (fun y : Dom n => gAmb (D (F t) i y) (deriv (fun r => F r y) t))
      x (basis j) = 0 :=
    fderiv_zero_of_forall_zero hzero x (basis j)
  rw [hasFDerivAt_gAmb_D hW hV j] at hfd0
  have hfd : gAmb (D (fun y => D (F t) i y) j x) (deriv (fun r => F r x) t)
      + gAmb (D (F t) i x) (D (fun y => deriv (fun r => F r y) t) j x) = 0 := hfd0
  have hcl := D_comm_x hF t x i j
  have hcomp : gAmb (D (fun y => D (F t) i y) j x) (deriv (fun r => F r x) t)
      = -(∑ k, w t x k * hTen (F t) i j k x) := by
    rw [hcl, hflow t x, gAmb_sum_right, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [gAmb_Iw_right]
    unfold hTen
    ring
  linarith [hfd, hcomp]

-- Main theorem
theorem solution {n : ℕ} (F : ℝ → Dom n → Amb n)
    (w : ℝ → Dom n → Fin n → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (hLag : ∀ s y, IsLagrangianAt (F s) y)
    (hflow : ∀ s y, deriv (fun r => F r y) s
      = ∑ k, (Complex.I * (w s y k : ℂ)) • D (F s) k y)
    (t : ℝ) (x : Dom n) (i j : Fin n) :
    deriv (fun s => gInd (F s) x i j) t
      = 2 * ∑ k, hTen (F t) i j k x * w t x k := by
  have hDi := hasDerivAt_D_comm hF t x i
  have hDj := hasDerivAt_D_comm hF t x j
  have hprod := hasDerivAt_gAmb_comp hDi hDj
  have hfun : (fun s => gInd (F s) x i j)
      = (fun s => gAmb (D (F s) i x) (D (F s) j x)) := by
    funext s
    rfl
  have hterm1 := term1 hF hLag hflow t x i j
  have hterm2 := term2 hF hLag hflow t x i j
  rw [hfun, hprod.deriv, hterm1, hterm2, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring
