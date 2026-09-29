-- Prove2me | solution 1 for SYZ.prop2_variation_of_pullback_kappa_oriented
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T16:18:21.714407+00:00
-- url     : https://prove2.me/submissions/f90b9215-10ad-43d4-aadc-4650e59c4fe2

import Mathlib
import Definitions.Def_syz_flat_model

/-! b34048a1 SYZ.prop2_variation_of_pullback_kappa_oriented (Strominger–Yau–Zaslow 1996, Section 3, Prop. 2).
With Φ(t,x) = F t x on ℝ × ℝⁿ, e_k = ∂_kF and V = ∂_tF:
* McLean's identity (Cramer's rule on the frame E, from the SYZ library): Re Ω(e) · √g g^{ij} θ_j
  = -|Re Ω(e)| · κ(e, i ← V); with Re Ω(e) > 0 this is J_i = -κ(e, i ← V).
* The multilinear derivative of κ gives ∂_t κ(e) = Σ_k κ(e, k ← ∂_t e_k) and
  ∂_i κ(e, i ← V) = Σ_k κ((e, i ← V), k ← ∂_i(column k)).
* Summed over i, the k ≠ i terms cancel in pairs (κ alternating, second derivatives symmetric), and the
  k = i terms are κ(e, i ← ∂_i V) = κ(e, i ← ∂_t e_i).  Hence -Σ_i ∂_i J_i = Σ_i ∂_i κ(e, i ← V) = ∂_t κ(e).
No `Theorems.*` module is imported. -/

set_option autoImplicit false

namespace SYZL

open SYZ Function

/-- the imaginary part of the holomorphic volume form, as a real multilinear map in columns -/
lemma kappa_update_eq {n : ℕ} [DecidableEq (Fin n)] (v : Fin n → Amb n) (i : Fin n) (x : Amb n) :
    kappa (Function.update v i x) =
      (((Matrix.of fun r k => v k r).updateCol i (WithLp.ofLp x)).det).im := by
  unfold kappa hVol
  congr 2
  ext r k
  by_cases h : k = i
  · subst h; simp
  · simp [h]

noncomputable def kappaML (n : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin n => Amb n) ℝ where
  toFun := kappa
  map_update_add' := by
    intro _ v i x y
    rw [kappa_update_eq, kappa_update_eq, kappa_update_eq]
    simp [WithLp.ofLp_add, Matrix.det_updateCol_add]
  map_update_smul' := by
    intro _ v i c x
    rw [kappa_update_eq, kappa_update_eq]
    have : WithLp.ofLp (c • x) = (c : ℂ) • WithLp.ofLp x := by
      ext r; simp [Complex.real_smul]
    rw [this, Matrix.det_updateCol_smul]
    simp [smul_eq_mul]
  cont := by
    unfold kappa hVol
    refine Complex.continuous_im.comp (Continuous.matrix_det ?_)
    refine continuous_matrix fun r k => ?_
    exact (PiLp.continuous_apply 2 _ r).comp (continuous_apply k)

@[simp] lemma kappaML_apply {n : ℕ} (v : Fin n → Amb n) : kappaML n v = kappa v := rfl

/-- derivative of `κ(DΦ·u₁, …, DΦ·uₙ)` -/
theorem hasFDerivAt_kappa_cols {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {n : ℕ}
    (Φ : P → Amb n) (hΦ : ContDiff ℝ 2 Φ) (u : Fin n → P) (p : P) :
    HasFDerivAt (fun q => kappa (fun k => fderiv ℝ Φ q (u k)))
      ((kappaML n).linearDeriv (fun k => fderiv ℝ Φ p (u k)) ∘L
        ContinuousLinearMap.pi (fun k => (fderiv ℝ (fderiv ℝ Φ) p).flip (u k))) p := by
  have hd : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hcols : HasFDerivAt (fun q => fun k => fderiv ℝ Φ q (u k))
      (ContinuousLinearMap.pi (fun k => (fderiv ℝ (fderiv ℝ Φ) p).flip (u k))) p := by
    refine hasFDerivAt_pi.2 fun k => ?_
    have := (hd p).hasFDerivAt.clm_apply (hasFDerivAt_const (u k) p)
    simpa using this
  exact ((kappaML n).hasFDerivAt _).comp p hcols

theorem fderiv_kappa_cols {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {n : ℕ}
    (Φ : P → Amb n) (hΦ : ContDiff ℝ 2 Φ) (u : Fin n → P) (p w : P) :
    fderiv ℝ (fun q => kappa (fun k => fderiv ℝ Φ q (u k))) p w =
      ∑ k, kappa (Function.update (fun k => fderiv ℝ Φ p (u k)) k
        (fderiv ℝ (fderiv ℝ Φ) p w (u k))) := by
  rw [(hasFDerivAt_kappa_cols Φ hΦ u p).fderiv]
  simp [ContinuousMultilinearMap.linearDeriv_apply]

/-! ## M5. alternating combinatorics: d(Φ^*κ) = 0 -/
/-- κ changes sign under a transposition of two columns -/
lemma kappa_swap {n : ℕ} (v : Fin n → Amb n) {i j : Fin n} (hij : i ≠ j) (x y : Amb n) :
    kappa (update (update v i x) j y) = -kappa (update (update v i y) j x) := by
  have hperm : ∀ u : Fin n → Amb n, kappa (u ∘ Equiv.swap i j) = -kappa u := by
    intro u
    unfold kappa hVol
    have : (Matrix.of fun r k => (u ∘ Equiv.swap i j) k r) =
        (Matrix.of fun r k => u k r).submatrix id (Equiv.swap i j) := by
      ext r k; rfl
    rw [this, Matrix.det_permute', Equiv.Perm.sign_swap hij]
    simp
  rw [← hperm]
  congr 1
  ext1 k
  simp only [Function.comp_apply]
  by_cases hki : k = i
  · subst hki; simp [Equiv.swap_apply_left, hij]
  · by_cases hkj : k = j
    · subst hkj; simp [Equiv.swap_apply_right, hij]
    · simp [Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj]

lemma sum_sum_antisymm {n : ℕ} (g : Fin n → Fin n → ℝ) (h : ∀ j k, g j k = -g k j) :
    ∑ j, ∑ k, g j k = 0 := by
  have h1 : ∑ j, ∑ k, g j k = -∑ j, ∑ k, g j k :=
    calc ∑ j, ∑ k, g j k = ∑ k, ∑ j, g j k := Finset.sum_comm
      _ = ∑ k, ∑ j, -g k j := Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => h j k
      _ = -∑ j, ∑ k, g j k := by simp only [Finset.sum_neg_distrib]
  linarith

lemma cols_update {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {n : ℕ}
    (L : P →L[ℝ] Amb n) (u : Fin n → P) (i : Fin n) (x : P) :
    (fun k => L (update u i x k)) = update (fun k => L (u k)) i (L x) := by
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [h]

/-! ## M6. McLean's identity (pointwise linear algebra) -/

lemma inner_eq_sum {n : ℕ} (u v : Amb n) :
    inner ℂ u v = ∑ r, (starRingEnd ℂ) (u r) * v r := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [mul_comm]

lemma gAmb_comm {n : ℕ} (u v : Amb n) : gAmb u v = gAmb v u := by
  unfold gAmb
  rw [← inner_conj_symm, Complex.conj_re]

/-- for a Lagrangian frame the Hermitian Gram matrix is the real Gram matrix -/
lemma inner_frame {n : ℕ} (e : Fin n → Amb n) (hLag : ∀ i j, kForm (e i) (e j) = 0) (k l : Fin n) :
    inner ℂ (e k) (e l) = ((gAmb (e k) (e l) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [gAmb]
  · simpa [kForm] using hLag k l

theorem detG_eq {n : ℕ} (e : Fin n → Amb n) (hLag : ∀ i j, kForm (e i) (e j) = 0)
    (hk : kappa e = 0) :
    (Matrix.of fun i j => gAmb (e i) (e j)).det = (hVol e).re ^ 2 := by
  set E : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun r k => e k r with hE
  set G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => gAmb (e i) (e j) with hG
  have hEE : E.conjTranspose * E = G.map (fun x : ℝ => (x : ℂ)) := by
    ext k l
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hE, Matrix.of_apply, Matrix.map_apply,
      hG]
    rw [← inner_frame e hLag k l, inner_eq_sum]
    rfl
  have hdet : ((G.det : ℝ) : ℂ) = (starRingEnd ℂ) E.det * E.det := by
    have h1 := RingHom.map_det Complex.ofRealHom G
    rw [RingHom.mapMatrix_apply] at h1
    have h2 : G.map ⇑Complex.ofRealHom = E.conjTranspose * E := by rw [hEE]; rfl
    rw [h2, Matrix.det_mul, Matrix.det_conjTranspose] at h1
    exact h1
  have hEv : E.det = hVol e := rfl
  have him : (hVol e).im = 0 := hk
  rw [← Complex.normSq_eq_conj_mul_self, hEv] at hdet
  have := congrArg Complex.re hdet
  simp only [Complex.ofReal_re] at this
  rw [this, Complex.normSq_apply, him]
  ring

/-- McLean's identity in coordinates: `J_i = √g g^{ij} θ_j` is `∓ κ(e, i ← V)`. -/
theorem mclean {n : ℕ} (e : Fin n → Amb n) (V : Amb n) (hLag : ∀ i j, kForm (e i) (e j) = 0)
    (hk : kappa e = 0) (hdet : (Matrix.of fun i j => gAmb (e i) (e j)).det ≠ 0) (i : Fin n) :
    (hVol e).re * (Real.sqrt (Matrix.of fun i j => gAmb (e i) (e j)).det *
      ∑ j, (Matrix.of fun i j => gAmb (e i) (e j))⁻¹ i j * kForm V (e j)) =
      -|(hVol e).re| * kappa (update e i V) := by
  set E : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun r k => e k r with hE
  set G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => gAmb (e i) (e j) with hG
  set re := (hVol e).re with hre
  have hdG : G.det = re ^ 2 := detG_eq e hLag hk
  have hre0 : re ≠ 0 := by
    intro h; apply hdet; rw [hdG, h]; ring
  have hEdet : E.det = (re : ℂ) := by
    apply Complex.ext
    · rfl
    · rw [Complex.ofReal_im]; exact hk
  have hEu : IsUnit E.det := by rw [hEdet]; exact (Complex.ofReal_ne_zero.2 hre0).isUnit
  have hGu : IsUnit G.det := hdet.isUnit
  set w : Fin n → ℂ := Matrix.mulVec E⁻¹ (WithLp.ofLp V) with hw
  have hEw : Matrix.mulVec E w = WithLp.ofLp V := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hEu, Matrix.one_mulVec]
  -- the κ side
  have hK : kappa (update e i V) = re * (w i).im := by
    rw [kappa_update_eq, ← hE, ← Matrix.cramer_apply]
    have hc : E.cramer (WithLp.ofLp V) = E.det • w := by
      have h1 := Matrix.mulVec_cramer E (WithLp.ofLp V)
      have h2 : Matrix.mulVec E⁻¹ (Matrix.mulVec E (E.cramer (WithLp.ofLp V))) = E.cramer (WithLp.ofLp V) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec]
      rw [← h2, h1, Matrix.mulVec_smul]
    rw [hc, Pi.smul_apply, smul_eq_mul, hEdet, Complex.im_ofReal_mul]
  -- the θ side
  have hθ : ∀ j, kForm V (e j) = -∑ k, G k j * (w k).im := by
    intro j
    have h1 : inner ℂ V (e j) = ∑ k, (starRingEnd ℂ) (w k) * ((G k j : ℝ) : ℂ) := by
      rw [inner_eq_sum]
      have hV : ∀ r, V r = ∑ k, E r k * w k := fun r => by
        rw [← hEw]; rfl
      simp only [hV, map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := inner_frame e hLag k j
      rw [inner_eq_sum] at this
      rw [hG, Matrix.of_apply, ← this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [hE, Matrix.of_apply]; ring
    unfold kForm
    rw [h1, Complex.im_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.conj_im, Complex.conj_re]
    ring
  have hJ : ∑ j, G⁻¹ i j * kForm V (e j) = -(w i).im := by
    simp only [hθ, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hsym : ∀ k j, G k j = G j k := fun k j => by simp [hG, gAmb_comm]
    have : ∀ k, ∑ j, G⁻¹ i j * (G k j * (w k).im) = (G⁻¹ * G) i k * (w k).im := by
      intro k
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hsym k j]; ring
    simp only [this, Matrix.nonsing_inv_mul _ hGu, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hJ, hK, hdG, Real.sqrt_sq_eq_abs]
  ring


end SYZL

namespace SYZP

open SYZ Function

variable {n : ℕ}

/-- the `x`-direction `j` and the `t`-direction in `ℝ × Dom n` -/
noncomputable def vx (n : ℕ) (j : Fin n) : ℝ × Dom n := (0, basis j)
noncomputable def vt (n : ℕ) : ℝ × Dom n := (1, 0)

lemma D_right' {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ × Dom n → V)
    (t : ℝ) (x : Dom n) (hd : DifferentiableAt ℝ h (t, x)) (j : Fin n) :
    D (fun y => h (t, y)) j x = fderiv ℝ h (t, x) (vx n j) := by
  have H : HasFDerivAt (fun y => h (t, y))
      ((fderiv ℝ h (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Dom n))) x :=
    hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  unfold D
  rw [H.fderiv]
  rfl

lemma deriv_left' {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ × Dom n → V)
    (t : ℝ) (x : Dom n) (hd : DifferentiableAt ℝ h (t, x)) :
    deriv (fun s => h (s, x)) t = fderiv ℝ h (t, x) (vt n) := by
  have H : HasFDerivAt (fun s => h (s, x))
      ((fderiv ℝ h (t, x)).comp (ContinuousLinearMap.inl ℝ ℝ (Dom n))) t :=
    hd.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)
  rw [H.hasDerivAt.deriv]
  rfl

/-- the family as a map on `ℝ × Dom n` -/
noncomputable def Phi (F : ℝ → Dom n → Amb n) : ℝ × Dom n → Amb n := fun p => F p.1 p.2

lemma DF_eq (F : ℝ → Dom n → Amb n) (hd : Differentiable ℝ (Phi F)) (s : ℝ) (x : Dom n)
    (j : Fin n) : D (F s) j x = fderiv ℝ (Phi F) (s, x) (vx n j) :=
  D_right' (Phi F) s x (hd _) j

lemma Dt_eq (F : ℝ → Dom n → Amb n) (hd : Differentiable ℝ (Phi F)) (t : ℝ) (x : Dom n) :
    deriv (fun s => F s x) t = fderiv ℝ (Phi F) (t, x) (vt n) :=
  deriv_left' (Phi F) t x (hd _)


/-- `κ(DΦ·u₁, …, DΦ·uₙ)` as a function on the parameter space -/
noncomputable def Kc {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : P → Amb n) (u : Fin n → P) : P → ℝ :=
  fun q => kappa (fun k => fderiv ℝ Φ q (u k))

lemma Kc_diff {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : P → Amb n) (hΦ : ContDiff ℝ 2 Φ) (u : Fin n → P) : Differentiable ℝ (Kc Φ u) :=
  fun p => (SYZL.hasFDerivAt_kappa_cols Φ hΦ u p).differentiableAt

lemma D_neg {k : ℕ} (g : Dom k → ℝ) (i : Fin k) (x : Dom k) :
    D (fun y => -g y) i x = -D g i x := by
  unfold D
  rw [fderiv_fun_neg]
  rfl

/-- the alternating cancellation behind `∂_t κ = Σ_i ∂_i κ(e, i ← ∂_t)` -/
theorem comb2 (A : (Fin n → Amb n) → ℝ)
    (hA : ∀ (v : Fin n → Amb n) (i j : Fin n) (x y : Amb n), i ≠ j →
      A (update (update v i x) j y) = -A (update (update v i y) j x))
    (a : Fin n → Amb n) (B : Amb n) (R : Fin n → Amb n) (Q : Fin n → Fin n → Amb n)
    (hQ : ∀ j k, Q j k = Q k j) :
    ∑ i, ∑ k, A (update (update a i B) k (if k = i then R i else Q i k)) =
      ∑ i, A (update a i (R i)) := by
  have hpt : ∀ i k, A (update (update a i B) k (if k = i then R i else Q i k)) =
      (if k = i then A (update a i (R i)) else 0) +
        (if k ≠ i then A (update (update a i B) k (Q i k)) else 0) := by
    intro i k
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  simp only [hpt, Finset.sum_add_distrib]
  rw [SYZL.sum_sum_antisymm (fun i k => if k ≠ i then A (update (update a i B) k (Q i k)) else 0) ?_]
  · simp
  · intro i k
    by_cases h : k = i
    · subst h; simp
    · rw [if_pos h, if_pos (Ne.symm h), update_comm h B (Q k i) a, hQ k i,
        hA a i k (Q i k) B (Ne.symm h), neg_neg]

theorem prop2o_lib (F : ℝ → Dom n → Amb n)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (hSL : ∀ y, IsSpecialLagrangianAt (F t) y)
    (him : ∀ y, (gInd (F t) y).det ≠ 0)
    (hor : ∀ y, 0 < (hVol (fun i => D (F t) i y)).re) (x : Dom n) :
    deriv (fun s => kappa (fun i => D (F s) i x)) t
      = -∑ i, D (fun y => volDens (F t) y
          * ∑ j, (gInd (F t) y)⁻¹ i j * theta1 F t y j) i x := by
  have hΦ : ContDiff ℝ 2 (Phi F) :=
    hF.of_le (by first | simp | exact WithTop.coe_le_coe.2 le_top)
  have hd : Differentiable ℝ (Phi F) := hΦ.differentiable (by norm_num)
  -- McLean with positive orientation: J_i = -κ(e, i ← ∂_tF)
  have hJ : ∀ i, (fun y => volDens (F t) y * ∑ j, (gInd (F t) y)⁻¹ i j * theta1 F t y j) =
      fun y => -Kc (Phi F) (update (vx n) i (vt n)) (t, y) := by
    intro i
    funext y
    have hs := hSL y
    have h := SYZL.mclean (fun k => D (F t) k y) (deriv (fun s => F s y) t) hs.1 hs.2 (him y) i
    have hK : kappa (update (fun k => D (F t) k y) i (deriv (fun s => F s y) t)) =
        Kc (Phi F) (update (vx n) i (vt n)) (t, y) := by
      unfold Kc
      rw [SYZL.cols_update (fderiv ℝ (Phi F) (t, y))]
      have hfr : (fun k => fderiv ℝ (Phi F) (t, y) (vx n k)) = fun k => D (F t) k y :=
        funext fun k => (DF_eq F hd t y k).symm
      rw [hfr, ← Dt_eq F hd t y]
    rw [abs_of_pos (hor y), hK] at h
    have e1 : volDens (F t) y * ∑ j, (gInd (F t) y)⁻¹ i j * theta1 F t y j =
        Real.sqrt (Matrix.of fun i j => gAmb (D (F t) i y) (D (F t) j y)).det *
          ∑ j, (Matrix.of fun i j => gAmb (D (F t) i y) (D (F t) j y))⁻¹ i j *
            kForm (deriv (fun s => F s y) t) (D (F t) j y) := rfl
    rw [e1]
    exact mul_left_cancel₀ (hor y).ne' (by rw [h]; ring)
  have hR : ∀ i, D (fun y => volDens (F t) y * ∑ j, (gInd (F t) y)⁻¹ i j * theta1 F t y j) i x =
      -fderiv ℝ (Kc (Phi F) (update (vx n) i (vt n))) (t, x) (vx n i) := by
    intro i
    rw [hJ i, D_neg, D_right' _ t x (Kc_diff _ hΦ _ _)]
  have hL : (fun s => kappa (fun i => D (F s) i x)) = fun s => Kc (Phi F) (vx n) (s, x) := by
    funext s
    unfold Kc
    congr 1
    funext k
    exact DF_eq F hd s x k
  have hs : ∀ v w, fderiv ℝ (fderiv ℝ (Phi F)) (t, x) v w =
      fderiv ℝ (fderiv ℝ (Phi F)) (t, x) w v :=
    hΦ.contDiffAt.isSymmSndFDerivAt (by simp)
  rw [hL, deriv_left' _ t x (Kc_diff _ hΦ _ _)]
  simp only [hR, Finset.sum_neg_distrib, neg_neg]
  unfold Kc
  rw [SYZL.fderiv_kappa_cols _ hΦ,
    Finset.sum_congr rfl fun i _ => SYZL.fderiv_kappa_cols (Phi F) hΦ _ (t, x) (vx n i)]
  set L := fderiv ℝ (Phi F) (t, x) with hLdef
  set D2 := fderiv ℝ (fderiv ℝ (Phi F)) (t, x) with hD2
  have e1 : ∀ i, (∑ k, kappa (update (fun k => L (update (vx n) i (vt n) k)) k
      (D2 (vx n i) (update (vx n) i (vt n) k)))) =
      ∑ k, kappa (update (update (fun k => L (vx n k)) i (L (vt n))) k
        (if k = i then D2 (vx n i) (vt n) else D2 (vx n i) (vx n k))) := by
    intro i
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [SYZL.cols_update]
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl fun i _ => e1 i,
    comb2 kappa (fun v i j x y h => SYZL.kappa_swap v h x y) _ _ _
      (fun j k => D2 (vx n j) (vx n k)) (fun j k => hs _ _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hs]

end SYZP

open SYZ in
theorem solution {n : ℕ} (F : ℝ → Dom n → Amb n)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (hSL : ∀ y, IsSpecialLagrangianAt (F t) y)
    (him : ∀ y, (gInd (F t) y).det ≠ 0)
    (hor : ∀ y, 0 < (hVol (fun i => D (F t) i y)).re) (x : Dom n) :
    deriv (fun s => kappa (fun i => D (F s) i x)) t
      = -∑ i, D (fun y => volDens (F t) y
          * ∑ j, (gInd (F t) y)⁻¹ i j * theta1 F t y j) i x := by
  exact SYZP.prop2o_lib F hF t hSL him hor x
