-- Prove2me | solution 1 for SYZ.eq34_moduli_metric_derivative_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T15:48:41.372265+00:00
-- url     : https://prove2.me/submissions/b018a653-6340-4fc8-8dc6-b0feceecb9ad

import Mathlib
import Definitions.Def_syz_flat_model

/-! 268deaf8 SYZ.eq34_moduli_metric_derivative_symmetric (Strominger–Yau–Zaslow 1996, Section 3).
Route (cohomological, no Hodge theory): with J^b_i = √g g^{ij} θ^b_j,
* McLean's pointwise identity (Cramer's rule on the frame E) gives J^b_i = σ·κ(e, i ← ∂_bF), with σ = ±1
  constant (Re hVol ≠ 0 on a connected space);
* the cohomology pairing ∫ θ·J = Σ_i (∫θ_i)(∫J_i) for closed periodic θ and divergence-free periodic J
  (translation trick: y ↦ ∫ θ(x+y)·J(x) dx has zero derivative, then Fubini + translation invariance;
  the only Stokes input is ∫_cube ∂_k W = 0 for periodic W, from the Mathlib divergence theorem);
* hence g_ab = σ Σ_i [θ^a]_i Y^b_i with [θ^a] constant (periodConst), and ∂_c Y^b_i = ∂_b Y^c_i from
  d(F^*κ) = 0 (alternating-multilinear derivative of κ + symmetry of second derivatives + the cube lemma);
* ∂_c g_ab is therefore symmetric in (b,c) and in (a,b), i.e. totally symmetric (eq34), and the
  moduli 2-form g_ab dt^a ∧ ds^b is closed.
No `Theorems.*` module is imported. -/

set_option autoImplicit false

namespace SYZL


open SYZ MeasureTheory Set Metric Function

/-! ## M1. closedness of the moduli Kähler form from derivative symmetry -/


/-- expand a vector of `Dom k` in the standard basis -/
lemma dom_expand {k : ℕ} (v : Dom k) : v = ∑ c, v c • basis c := by
  ext i
  simp [basis, Finset.sum_apply, Pi.single_apply]

lemma fderiv_expand {k : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h : Dom k → V) (t v : Dom k) : fderiv ℝ h t v = ∑ c, v c • D h c t := by
  conv_lhs => rw [dom_expand v]
  simp [map_sum, map_smul, D]

lemma sum3_swap13 {m : ℕ} (f : Fin m → Fin m → Fin m → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ b, ∑ c, f c b a := by
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

theorem closed_of_symm {m : ℕ} (g : Dom m → Matrix (Fin m) (Fin m) ℝ)
    (hdiff : ∀ a b, Differentiable ℝ (fun t => g t a b))
    (hsym : ∀ (a b c : Fin m) (t : Dom m),
      D (fun s => g s b c) a t = D (fun s => g s a c) b t) :
    IsClosed2Form (moduliKahler g) := by
  intro p X Y Z
  have key : ∀ (U V W : Mod m), fderiv ℝ (fun q => moduliKahler g q V W) p U =
      ∑ a, ∑ b, ∑ c, U.1 c * D (fun s => g s a b) c p.1 * (V.1 a * W.2 b - W.1 a * V.2 b) := by
    intro U V W
    have hd : ∀ a b, HasFDerivAt (fun q : Mod m => g q.1 a b)
        ((fderiv ℝ (fun t => g t a b) p.1).comp (ContinuousLinearMap.fst ℝ (Dom m) (Dom m))) p :=
      fun a b => ((hdiff a b) p.1).hasFDerivAt.comp p hasFDerivAt_fst
    have H : HasFDerivAt (fun q => moduliKahler g q V W)
        (∑ a, ∑ b, (V.1 a * W.2 b - W.1 a * V.2 b) •
          ((fderiv ℝ (fun t => g t a b) p.1).comp (ContinuousLinearMap.fst ℝ (Dom m) (Dom m)))) p := by
      unfold moduliKahler
      refine HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ => ?_
      have := (hd a b).mul_const (V.1 a * W.2 b - W.1 a * V.2 b)
      convert this using 1
    rw [H.fderiv]
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_fst', smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [fderiv_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [smul_eq_mul]; ring
  unfold d2
  rw [key, key, key]
  -- S a b c = D g_ab in direction c ; symmetric in a,c
  set S : Fin m → Fin m → Fin m → ℝ := fun a b c => D (fun s => g s a b) c p.1 with hS
  have hS' : ∀ a b c, S a b c = S c b a := fun a b c => hsym c a b p.1
  have e1 : ∑ a, ∑ b, ∑ c, X.1 c * S a b c * (Y.1 a * Z.2 b) =
      ∑ a, ∑ b, ∑ c, Y.1 c * S a b c * (X.1 a * Z.2 b) := by
    rw [sum3_swap13]; simp only [hS']; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl
      fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have e2 : ∑ a, ∑ b, ∑ c, Y.1 c * S a b c * (Z.1 a * X.2 b) =
      ∑ a, ∑ b, ∑ c, Z.1 c * S a b c * (Y.1 a * X.2 b) := by
    rw [sum3_swap13]; simp only [hS']; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl
      fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have e3 : ∑ a, ∑ b, ∑ c, Z.1 c * S a b c * (X.1 a * Y.2 b) =
      ∑ a, ∑ b, ∑ c, X.1 c * S a b c * (Z.1 a * Y.2 b) := by
    rw [sum3_swap13]; simp only [hS']; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl
      fun b _ => Finset.sum_congr rfl fun c _ => by ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [e1, e2, e3]; ring


/-! ## M2. the unit cube: transfer, compactness, volume, divergence-free lemma -/


lemma toLp_preimage_cube (n : ℕ) :
    (WithLp.toLp 2 : (Fin n → ℝ) → Dom n) ⁻¹' cube n = Icc 0 1 := by
  ext y; simp [cube, Set.mem_Icc, Pi.le_def, forall_and]

lemma integral_cube_eq (n : ℕ) (f : Dom n → ℝ) :
    ∫ x in cube n, f x = ∫ y in Icc (0 : Fin n → ℝ) 1, f (WithLp.toLp 2 y) := by
  rw [← toLp_preimage_cube]
  exact ((PiLp.volume_preserving_toLp (Fin n)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding f (cube n)).symm

lemma cube_eq_image (n : ℕ) : cube n = (WithLp.toLp 2 : (Fin n → ℝ) → Dom n) '' Icc 0 1 := by
  rw [← toLp_preimage_cube, Set.image_preimage_eq]
  intro x; exact ⟨WithLp.ofLp x, rfl⟩

lemma isCompact_cube (n : ℕ) : IsCompact (cube n) := by
  rw [cube_eq_image]
  exact isCompact_Icc.image (PiLp.continuous_toLp 2 _)

lemma measurableSet_cube (n : ℕ) : MeasurableSet (cube n) :=
  (isCompact_cube n).isClosed.measurableSet

lemma volume_cube (n : ℕ) : volume (cube n) = 1 := by
  have := (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (measurableSet_cube n).nullMeasurableSet
  rw [toLp_preimage_cube] at this
  rw [← this, Real.volume_Icc_pi]
  simp

lemma insertNth_one_eq {n : ℕ} (k : Fin (n + 1)) (x : Fin n → ℝ) :
    Fin.insertNth (α := fun _ => ℝ) k 1 x = Fin.insertNth (α := fun _ => ℝ) k 0 x + Pi.single k 1 := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨j, rfl⟩
  · simp
  · simp [Pi.single_apply, Fin.succAbove_ne]

/-- The integral of a partial derivative of a periodic `C¹` function over the unit cube is 0. -/
theorem integral_cube_D_eq_zero {n : ℕ} (W : Dom n → ℝ) (hW : ContDiff ℝ 1 W)
    (hper : ∀ a x, W (x + basis a) = W x) (k : Fin n) :
    ∫ x in cube n, D W k x = 0 := by
  cases n with
  | zero => exact k.elim0
  | succ n =>
  set e := EuclideanSpace.equiv (Fin (n + 1)) ℝ
  set W' : (Fin (n + 1) → ℝ) → ℝ := fun y => W (WithLp.toLp 2 y) with hW'
  have hW'd : ContDiff ℝ 1 W' := hW.comp (e.symm.contDiff)
  have hder : ∀ y, D W k (WithLp.toLp 2 y) = fderiv ℝ W' y (Pi.single k 1) := by
    intro y
    have h1 : HasFDerivAt W' ((fderiv ℝ W (WithLp.toLp 2 y)).comp (e.symm : _ →L[ℝ] _)) y :=
      ((hW.differentiable (by norm_num)) _).hasFDerivAt.comp y e.symm.hasFDerivAt
    rw [h1.fderiv]; rfl
  rw [integral_cube_eq]
  simp_rw [hder]
  have hsum : ∀ y, (∑ i, (if i = k then fderiv ℝ W' y else 0) (Pi.single i 1)) =
      fderiv ℝ W' y (Pi.single k 1) := by
    intro y
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable' (0 : Fin (n + 1) → ℝ) 1
    zero_le_one (fun i => if i = k then W' else 0)
    (fun i y => if i = k then fderiv ℝ W' y else 0) ∅ countable_empty
    (fun i => by split_ifs <;> [exact hW'd.continuous.continuousOn; exact continuousOn_const])
    (fun y _ i => by
      split_ifs
      · exact ((hW'd.differentiable (by norm_num)) y).hasFDerivAt
      · exact hasFDerivAt_const _ _)
    (by
      simp_rw [hsum]
      exact ((hW'd.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn
        |>.integrableOn_compact isCompact_Icc)
  simp_rw [hsum] at hdiv
  rw [hdiv]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hik : i = k
  · subst hik
    simp only [if_true, Pi.one_apply, Pi.zero_apply]
    rw [sub_eq_zero]
    refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
    simp only [hW', insertNth_one_eq, WithLp.toLp_add]
    exact hper i _
  · simp [hik]


/-! ## M3. differentiation under the integral; M4. κ as a multilinear map -/


instance (n : ℕ) : IsFiniteMeasure (volume.restrict (cube n)) :=
  isFiniteMeasure_restrict.2 (isCompact_cube n).measure_lt_top.ne

/-- differentiation under the integral over the cube, jointly `C¹` integrand -/
theorem hasFDerivAt_integral_cube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {n : ℕ} (G : E → Dom n → ℝ)
    (hG : ContDiff ℝ 1 (fun p : E × Dom n => G p.1 p.2)) (t : E) :
    HasFDerivAt (fun s => ∫ x in cube n, G s x)
      (∫ x in cube n, fderiv ℝ (fun s => G s x) t) t := by
  have hF'c : Continuous (fun p : E × Dom n => fderiv ℝ (fun s => G s p.2) p.1) := by
    have h1 : ContDiff ℝ 1 (Function.uncurry fun (p : E × Dom n) (s : E) => G s p.2) :=
      hG.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
    exact (ContDiff.fderiv (n := 0) h1 contDiff_fst (by norm_num)).continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t 1).prod (isCompact_cube n)).exists_bound_of_continuousOn
    hF'c.continuousOn
  have hGc : ∀ s, Continuous (G s) := fun s =>
    hG.continuous.comp (continuous_const.prodMk continuous_id)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict (cube n))
    (bound := fun _ => C) (ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun s => (hGc s).aestronglyMeasurable)
    ((hGc t).continuousOn.integrableOn_compact (isCompact_cube n))
    (hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    ((ae_restrict_iff' (measurableSet_cube n)).2 (Filter.Eventually.of_forall fun x hx s hs =>
      hC (s, x) ⟨ball_subset_closedBall hs, hx⟩))
    (integrable_const C)
    (Filter.Eventually.of_forall fun x s _ => ?_)
  have : ContDiff ℝ 1 (fun s => G s x) := hG.comp (contDiff_id.prodMk contDiff_const)
  exact ((this.differentiable (by norm_num)) s).hasFDerivAt

theorem D_integral_cube {m n : ℕ} (G : Dom m → Dom n → ℝ)
    (hG : ContDiff ℝ 1 (fun p : Dom m × Dom n => G p.1 p.2)) (c : Fin m) (t : Dom m) :
    D (fun s => ∫ x in cube n, G s x) c t = ∫ x in cube n, D (fun s => G s x) c t := by
  have hF'c : Continuous (fun x : Dom n => fderiv ℝ (fun s => G s x) t) := by
    have h1 : ContDiff ℝ 1 (Function.uncurry fun (x : Dom n) (s : Dom m) => G s x) :=
      hG.comp (contDiff_snd.prodMk contDiff_fst)
    exact (ContDiff.fderiv (n := 0) h1 (contDiff_const (c := t)) (by norm_num)).continuous
  unfold D
  rw [(hasFDerivAt_integral_cube G hG t).fderiv,
    ContinuousLinearMap.integral_apply (hF'c.continuousOn.integrableOn_compact (isCompact_cube n))]

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

/-- the alternating-sum cancellation behind `d(F^*κ) = 0` -/
theorem comb {n : ℕ} (A : (Fin n → Amb n) → ℝ)
    (hA : ∀ (v : Fin n → Amb n) (i j : Fin n) (x y : Amb n), i ≠ j →
      A (update (update v i x) j y) = -A (update (update v i y) j x))
    (a : Fin n → Amb n) (B C R : Amb n) (M N : Fin n → Amb n)
    (Q : Fin n → Fin n → Amb n) (hQ : ∀ j k, Q j k = Q k j) (i : Fin n) :
    (∑ k, A (update (update a i B) k (if k = i then R else M k)))
      - ∑ k, A (update (update a i C) k (if k = i then R else N k)) =
    ∑ j ∈ Finset.univ.erase i, ∑ k, A (update (update (update a i B) j C) k
        (if k = i then N j else if k = j then M j else Q j k)) := by
  classical
  -- split the left sums at k = i
  have hL : ∀ (D : Amb n) (L : Fin n → Amb n), (∑ k, A (update (update a i D) k
      (if k = i then R else L k))) = A (update a i R) +
        ∑ k, (if k ≠ i then A (update (update a i D) k (L k)) else 0) := by
    intro D L
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [if_true, update_idem]
    congr 1
    rw [← Finset.sum_filter, Finset.filter_ne']
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_neg (Finset.ne_of_mem_erase hk)]
  -- split each inner right sum at k = i and k = j
  have hR : ∀ j, j ≠ i → (∑ k, A (update (update (update a i B) j C) k
        (if k = i then N j else if k = j then M j else Q j k))) =
      A (update (update a i B) j (M j)) - A (update (update a i C) j (N j)) +
        ∑ k, (if k ≠ i ∧ k ≠ j then A (update (update (update a i B) j C) k (Q j k)) else 0) := by
    intro j hji
    have hpt : ∀ k, A (update (update (update a i B) j C) k
        (if k = i then N j else if k = j then M j else Q j k)) =
        (if k = j then A (update (update a i B) j (M j)) else 0)
        + (if k = i then -A (update (update a i C) j (N j)) else 0)
        + (if k ≠ i ∧ k ≠ j then A (update (update (update a i B) j C) k (Q j k)) else 0) := by
      intro k
      by_cases hki : k = i
      · subst hki
        rw [if_pos rfl, if_neg (Ne.symm hji), if_pos rfl, if_neg (by tauto)]
        rw [update_comm hji, update_idem, hA a k j (N j) C (Ne.symm hji)]
        ring
      · by_cases hkj : k = j
        · subst hkj
          rw [if_neg hki, if_pos rfl, if_pos rfl, if_neg hki, if_neg (by tauto), update_idem]
          ring
        · rw [if_neg hki, if_neg hkj, if_neg hkj, if_neg hki, if_pos ⟨hki, hkj⟩]
          ring
    rw [Finset.sum_congr rfl fun k _ => hpt k, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    ring
  rw [hL, hL, Finset.sum_congr rfl fun j hj => hR j (Finset.ne_of_mem_erase hj),
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- the double sum vanishes by antisymmetry
  have hdouble : ∑ j ∈ Finset.univ.erase i, ∑ k, (if k ≠ i ∧ k ≠ j then
      A (update (update (update a i B) j C) k (Q j k)) else 0) = 0 := by
    rw [← Finset.filter_ne', Finset.sum_filter]
    have := sum_sum_antisymm (fun j k => if j ≠ i ∧ k ≠ i ∧ k ≠ j then
      A (update (update (update a i B) j C) k (Q j k)) else 0) (by
        intro j k
        by_cases h : j ≠ i ∧ k ≠ i ∧ k ≠ j
        · rw [if_pos h, if_pos ⟨h.2.1, h.1, Ne.symm h.2.2⟩,
            hA _ j k C (Q j k) (Ne.symm h.2.2), update_comm (Ne.symm h.2.2), hQ]
        · rw [if_neg h, if_neg (by tauto), neg_zero])
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ≠ i
    · rw [if_pos hj]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : k ≠ i ∧ k ≠ j
      · rw [if_pos hk, if_pos ⟨hj, hk⟩]
      · rw [if_neg hk, if_neg (by tauto)]
    · rw [if_neg hj]
      symm; refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg (by tauto)]
  rw [hdouble]
  rw [← Finset.filter_ne', Finset.sum_filter, Finset.sum_filter]
  ring

lemma cols_update {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {n : ℕ}
    (L : P →L[ℝ] Amb n) (u : Fin n → P) (i : Fin n) (x : P) :
    (fun k => L (update u i x k)) = update (fun k => L (u k)) i (L x) := by
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [h]

/-- `d(Φ^*κ) = 0`, the component with two extra directions `β, γ` replacing column `i`. -/
theorem dFkappa {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {n : ℕ}
    (Φ : P → Amb n) (hΦ : ContDiff ℝ 2 Φ) (vx : Fin n → P) (β γ : P) (i : Fin n) (p : P) :
    fderiv ℝ (fun q => kappa (fun k => fderiv ℝ Φ q (update vx i β k))) p γ
      - fderiv ℝ (fun q => kappa (fun k => fderiv ℝ Φ q (update vx i γ k))) p β =
    ∑ j ∈ Finset.univ.erase i,
      fderiv ℝ (fun q => kappa (fun k => fderiv ℝ Φ q (update (update vx i β) j γ k))) p (vx j) := by
  have hs : ∀ v w, fderiv ℝ (fderiv ℝ Φ) p v w = fderiv ℝ (fderiv ℝ Φ) p w v :=
    hΦ.contDiffAt.isSymmSndFDerivAt (by simp)
  rw [fderiv_kappa_cols Φ hΦ, fderiv_kappa_cols Φ hΦ,
    Finset.sum_congr rfl fun j _ => fderiv_kappa_cols Φ hΦ _ p (vx j)]
  set L := fderiv ℝ Φ p with hLdef
  set D2 := fderiv ℝ (fderiv ℝ Φ) p with hD2
  have e1 : ∀ w x, (∑ k, kappa (update (fun k => L (update vx i x k)) k (D2 w (update vx i x k)))) =
      ∑ k, kappa (update (update (fun k => L (vx k)) i (L x)) k
        (if k = i then D2 w x else D2 w (vx k))) := by
    intro w x
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cols_update]
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  rw [e1, e1, hs β γ]
  rw [comb kappa (fun v i j x y h => kappa_swap v h x y) (fun k => L (vx k)) (L β) (L γ)
    (D2 γ β) (fun k => D2 γ (vx k)) (fun k => D2 β (vx k)) (fun j k => D2 (vx j) (vx k))
    (fun j k => hs _ _) i]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k _ => ?_
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  rw [cols_update, cols_update]
  congr 2
  by_cases hki : k = i
  · subst hki; simp [Ne.symm hji, hs]
  · by_cases hkj : k = j
    · subst hkj; simp [hki, hs]
    · simp [hki, hkj]


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


/-! ## M7. constant sign on a connected space -/

lemma sign_const {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] (s : X → ℝ)
    (hs : Continuous s) (h0 : ∀ x, s x ≠ 0) : (∀ x, 0 < s x) ∨ (∀ x, s x < 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hcon
  have hx' : s x < 0 := lt_of_le_of_ne hx (h0 x)
  have hy' : 0 < s y := lt_of_le_of_ne hy (h0 y).symm
  obtain ⟨z, -, hz⟩ := isPreconnected_univ.intermediate_value (mem_univ x) (mem_univ y)
    hs.continuousOn ⟨hx'.le, hy'.le⟩
  exact h0 z hz

/-! ## M8. the cohomology pairing on the torus (translation trick) -/

lemma intOn_cube {n : ℕ} {f : Dom n → ℝ} (hf : Continuous f) : IntegrableOn f (cube n) :=
  hf.continuousOn.integrableOn_compact (isCompact_cube n)

/-- a parametric cube integral whose parameter-derivatives integrate to zero is constant -/
lemma const_of_D_integral {n : ℕ} (G : Dom n → Dom n → ℝ)
    (hG : ContDiff ℝ 1 (fun p : Dom n × Dom n => G p.1 p.2))
    (h : ∀ x c, ∫ y in cube n, D (fun s => G s y) c x = 0) (x x' : Dom n) :
    ∫ y in cube n, G x y = ∫ y in cube n, G x' y := by
  refine is_const_of_fderiv_eq_zero (f := fun x => ∫ y in cube n, G x y)
    (fun x => (hasFDerivAt_integral_cube G hG x).differentiableAt) (fun x => ?_) x x'
  ext1 v
  rw [fderiv_expand]
  simp [D_integral_cube G hG, h]

lemma D_comp_add_left {n : ℕ} (g : Dom n → ℝ) (x : Dom n) (c : Fin n) (y : Dom n) :
    D (fun s => g (x + s)) c y = D g c (x + y) := by
  unfold D; rw [fderiv_comp_add_left]

lemma D_comp_add_right {n : ℕ} (g : Dom n → ℝ) (y : Dom n) (c : Fin n) (x : Dom n) :
    D (fun s => g (s + y)) c x = D g c (x + y) := by
  unfold D; rw [fderiv_comp_add_right]

/-- translation invariance of the torus integral of a periodic function -/
theorem transl_inv {n : ℕ} (g : Dom n → ℝ) (hg : ContDiff ℝ 1 g)
    (hper : ∀ a x, g (x + basis a) = g x) (x : Dom n) :
    ∫ y in cube n, g (x + y) = ∫ y in cube n, g y := by
  have hG : ContDiff ℝ 1 (fun p : Dom n × Dom n => g (p.1 + p.2)) :=
    hg.comp (contDiff_fst.add contDiff_snd)
  have := const_of_D_integral (fun x y => g (x + y)) hG (fun x c => by
    simp only [D_comp_add_right]
    have := integral_cube_D_eq_zero (fun y => g (x + y)) (hg.comp (contDiff_const.add contDiff_id))
      (fun a y => by simp only [← add_assoc, hper]) c
    simpa [D_comp_add_left] using this) x 0
  simpa using this

/-- **Cohomology pairing.** For a closed periodic 1-form `θ` and a periodic divergence-free field
`J`, `∫ θ·J = Σᵢ (∫ θᵢ)(∫ Jᵢ)`. -/
theorem pairing {n : ℕ} (θ J : Dom n → Fin n → ℝ)
    (hθ : ∀ i, ContDiff ℝ 1 (fun x => θ x i)) (hJ : ∀ i, ContDiff ℝ 1 (fun x => J x i))
    (hθp : ∀ a x i, θ (x + basis a) i = θ x i) (hJp : ∀ a x i, J (x + basis a) i = J x i)
    (hcl : IsClosed1Form θ) (hdiv : ∀ x, ∑ i, D (fun y => J y i) i x = 0) :
    ∫ x in cube n, ∑ i, θ x i * J x i =
      ∑ i, (∫ x in cube n, θ x i) * (∫ x in cube n, J x i) := by
  set Ψ : Dom n → Dom n → ℝ := fun y x => ∑ i, θ (x + y) i * J x i with hΨ
  have hΨc : ContDiff ℝ 1 (fun p : Dom n × Dom n => Ψ p.1 p.2) :=
    ContDiff.sum fun i _ => ((hθ i).comp (contDiff_snd.add contDiff_fst)).mul
      ((hJ i).comp contDiff_snd)
  have hθd : ∀ i, Differentiable ℝ (fun x => θ x i) := fun i => (hθ i).differentiable (by norm_num)
  have hJd : ∀ i, Differentiable ℝ (fun x => J x i) := fun i => (hJ i).differentiable (by norm_num)
  have hWc : ∀ y c i, ContDiff ℝ 1 (fun z => θ (z + y) c * J z i) := fun y c i =>
    ((hθ c).comp (contDiff_id.add contDiff_const)).mul (hJ i)
  -- Step A: the parameter derivative integrates to zero
  have hA : ∀ y c, ∫ x in cube n, D (fun s => Ψ s x) c y = 0 := by
    intro y c
    have h1 : ∀ x, D (fun s => Ψ s x) c y = ∑ i, D (fun z => θ z i) c (x + y) * J x i := by
      intro x
      have hdθx : ∀ i, Differentiable ℝ (fun s => θ (x + s) i) := fun i =>
        (hθd i).comp ((differentiable_const x).add differentiable_id)
      unfold D
      simp only [hΨ]
      rw [fderiv_fun_sum (A := fun i s => θ (x + s) i * J x i)
        (fun i _ => ((hdθx i).mul_const (J x i)) y)]
      simp only [FunLike.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [fderiv_mul_const ((hdθx i) y)]
      simp only [smul_apply, smul_eq_mul]
      have := D_comp_add_left (fun z => θ z i) x c y
      unfold D at this
      rw [this, mul_comm]
    have hprod : ∀ x i, D (fun z => θ (z + y) c * J z i) i x =
        D (fun z => θ z c) i (x + y) * J x i + θ (x + y) c * D (fun z => J z i) i x := by
      intro x i
      have hdθy : Differentiable ℝ (fun z => θ (z + y) c) :=
        (hθd c).comp (differentiable_id.add_const y)
      unfold D
      rw [fderiv_fun_mul (hdθy x) ((hJd i) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      have := D_comp_add_right (fun z => θ z c) y i x
      unfold D at this
      rw [this]; ring
    have hpt : ∀ x, D (fun s => Ψ s x) c y = ∑ i, D (fun z => θ (z + y) c * J z i) i x := by
      intro x
      rw [h1 x]
      simp only [hprod x, Finset.sum_add_distrib, ← Finset.mul_sum, hdiv x, mul_zero, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcl c i (x + y)]
    simp only [hpt]
    rw [integral_finsetSum (f := fun i x => D (fun z => θ (z + y) c * J z i) i x) _
      (fun i _ => intOn_cube
        (((hWc y c i).continuous_fderiv (by norm_num)).clm_apply continuous_const))]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine integral_cube_D_eq_zero _ (hWc y c i) (fun a z => ?_) i
    simp only [add_right_comm z (basis a) y, hθp, hJp]
  -- Step B: Ψ y integrates to the same value for every y
  have hB : ∀ y, ∫ x in cube n, Ψ y x = ∫ x in cube n, Ψ 0 x := fun y =>
    const_of_D_integral Ψ hΨc hA y 0
  have hΨcont : Continuous (fun p : Dom n × Dom n => Ψ p.1 p.2) := hΨc.continuous
  -- Step C: Fubini
  have hint : Integrable (Function.uncurry Ψ)
      ((volume.restrict (cube n)).prod (volume.restrict (cube n))) := by
    rw [Measure.prod_restrict]
    exact hΨcont.continuousOn.integrableOn_compact ((isCompact_cube n).prod (isCompact_cube n))
  have hfub := integral_integral_swap hint
  have hL : ∫ y in cube n, ∫ x in cube n, Ψ y x = ∫ x in cube n, Ψ 0 x := by
    simp only [hB, setIntegral_const, measureReal_def, volume_cube]
    simp
  have hR : ∫ x in cube n, ∫ y in cube n, Ψ y x =
      ∑ i, (∫ x in cube n, θ x i) * (∫ x in cube n, J x i) := by
    have hin : ∀ x, ∫ y in cube n, Ψ y x = ∑ i, (∫ z in cube n, θ z i) * J x i := by
      intro x
      simp only [hΨ]
      rw [integral_finsetSum (f := fun i y => θ (x + y) i * J x i) _ (fun i _ => intOn_cube
        ((((hθ i).continuous.comp (continuous_const.add continuous_id))).mul continuous_const))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_mul_const]
      congr 1
      have := transl_inv (fun z => θ z i) (hθ i) (fun a z => hθp a z i) x
      simpa [add_comm] using this
    simp only [hin]
    rw [integral_finsetSum (f := fun i x => (∫ z in cube n, θ z i) * J x i) _
      (fun i _ => intOn_cube (continuous_const.mul (hJ i).continuous))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  rw [← hR, ← hfub, hL]
  simp [hΨ]

/-! ## M9. SYZ glue -/

section Glue

variable {n m : ℕ}

/-- `x`-direction `j` and `t`-direction `a` in `Dom m × Dom n` -/
noncomputable def vX (m : ℕ) {n : ℕ} (j : Fin n) : Dom m × Dom n := (0, basis j)
noncomputable def vT {m : ℕ} (n : ℕ) (a : Fin m) : Dom m × Dom n := (basis a, 0)

lemma D_right {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : Dom m × Dom n → V)
    (t : Dom m) (x : Dom n) (hd : DifferentiableAt ℝ h (t, x)) (j : Fin n) :
    D (fun y => h (t, y)) j x = fderiv ℝ h (t, x) (vX m j) := by
  have H : HasFDerivAt (fun y => h (t, y))
      ((fderiv ℝ h (t, x)).comp (ContinuousLinearMap.inr ℝ (Dom m) (Dom n))) x :=
    hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  unfold D
  rw [H.fderiv]
  rfl

lemma D_left {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : Dom m × Dom n → V)
    (t : Dom m) (x : Dom n) (hd : DifferentiableAt ℝ h (t, x)) (a : Fin m) :
    D (fun s => h (s, x)) a t = fderiv ℝ h (t, x) (vT n a) := by
  have H : HasFDerivAt (fun s => h (s, x))
      ((fderiv ℝ h (t, x)).comp (ContinuousLinearMap.inl ℝ (Dom m) (Dom n))) t :=
    hd.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)
  unfold D
  rw [H.fderiv]
  rfl

/-- the family as a map on `Dom m × Dom n` -/
noncomputable def Phi (S : SYZFamily n m) : Dom m × Dom n → Amb n := fun p => S.F p.1 p.2

lemma Phi_smooth (S : SYZFamily n m) : ContDiff ℝ 2 (Phi S) :=
  S.smooth.of_le (by first | simp | exact WithTop.coe_le_coe.2 le_top)

lemma Phi_diff (S : SYZFamily n m) : Differentiable ℝ (Phi S) :=
  (Phi_smooth S).differentiable (by norm_num)

lemma cols_smooth (S : SYZFamily n m) (u : Dom m × Dom n) :
    ContDiff ℝ 1 (fun p => fderiv ℝ (Phi S) p u) :=
  ((Phi_smooth S).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

lemma DF_eq (S : SYZFamily n m) (t : Dom m) (x : Dom n) (j : Fin n) :
    D (S.F t) j x = fderiv ℝ (Phi S) (t, x) (vX m j) :=
  D_right (Phi S) t x (Phi_diff S _) j

lemma DFt_eq (S : SYZFamily n m) (t : Dom m) (x : Dom n) (a : Fin m) :
    D (fun s => S.F s x) a t = fderiv ℝ (Phi S) (t, x) (vT n a) :=
  D_left (Phi S) t x (Phi_diff S _) a

lemma thetaM_eq (S : SYZFamily n m) (a : Fin m) (t : Dom m) (x : Dom n) (i : Fin n) :
    thetaM S.F a t x i = kForm (fderiv ℝ (Phi S) (t, x) (vT n a)) (fderiv ℝ (Phi S) (t, x) (vX m i)) := by
  unfold thetaM; rw [DF_eq, DFt_eq]

/-- the derivative of the family is periodic in `x` -/
lemma fderiv_Phi_periodic (S : SYZFamily n m) (t : Dom m) (x : Dom n) (a : Fin n) :
    fderiv ℝ (Phi S) (t, x + basis a) = fderiv ℝ (Phi S) (t, x) := by
  have h1 : (fun q : Dom m × Dom n => Phi S (q + (0, basis a))) = fun q => Phi S q + S.lam a := by
    funext q; simp only [Phi, Prod.fst_add, Prod.snd_add, add_zero]; exact S.periodic q.1 a q.2
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := Phi S) (x := (t, x)) ((0 : Dom m), basis a)
  rw [h1, fderiv_add_const] at h2
  have h3 : (t, x) + ((0 : Dom m), basis a) = (t, x + basis a) := by simp
  rw [h3] at h2
  exact h2.symm

lemma kForm_smooth {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (f g : P → Amb n)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) : ContDiff ℝ 1 (fun p => kForm (f p) (g p)) :=
  Complex.imCLM.contDiff.comp (hf.inner ℂ hg)

lemma theta_smooth (S : SYZFamily n m) (a : Fin m) (i : Fin n) :
    ContDiff ℝ 1 (fun p : Dom m × Dom n => thetaM S.F a p.1 p.2 i) := by
  simp only [thetaM_eq]
  exact kForm_smooth _ _ (cols_smooth S _) (cols_smooth S _)

/-- `κ` evaluated on a column list of directional derivatives -/
noncomputable def Kf (S : SYZFamily n m) (u : Fin n → Dom m × Dom n) : Dom m × Dom n → ℝ :=
  fun p => kappa (fun k => fderiv ℝ (Phi S) p (u k))

lemma Kf_smooth (S : SYZFamily n m) (u : Fin n → Dom m × Dom n) : ContDiff ℝ 1 (Kf S u) :=
  (kappaML n).contDiff.comp (contDiff_pi.2 fun k => cols_smooth S (u k))

lemma Kf_periodic (S : SYZFamily n m) (u : Fin n → Dom m × Dom n) (t : Dom m) (x : Dom n)
    (a : Fin n) : Kf S u (t, x + basis a) = Kf S u (t, x) := by
  simp only [Kf, fderiv_Phi_periodic]

/-- the orientation function `Re Ω(∂₁F, …, ∂ₙF)` -/
noncomputable def reVol (S : SYZFamily n m) (p : Dom m × Dom n) : ℝ :=
  (hVol (fun k => fderiv ℝ (Phi S) p (vX m k))).re

lemma frame_eq (S : SYZFamily n m) (t : Dom m) (x : Dom n) :
    (fun k => fderiv ℝ (Phi S) (t, x) (vX m k)) = fun k => D (S.F t) k x := by
  funext k; rw [DF_eq]

lemma reVol_ne (S : SYZFamily n m) (p : Dom m × Dom n) : reVol S p ≠ 0 := by
  intro h
  have hs := S.slag p.1 p.2
  have hd := detG_eq (fun k => D (S.F p.1) k p.2) hs.1 hs.2
  apply S.immersed p.1 p.2
  unfold gInd
  rw [hd]
  have : (hVol fun k => D (S.F p.1) k p.2).re = reVol S p := by
    unfold reVol; rw [frame_eq]
  rw [this, h]; ring

lemma reVol_cont (S : SYZFamily n m) : Continuous (reVol S) := by
  unfold reVol hVol
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine continuous_matrix fun r k => ?_
  exact (PiLp.continuous_apply 2 _ r).comp (cols_smooth S (vX m k)).continuous

/-- McLean at the level of functions, with a global sign `σ` -/
theorem mclean_family (S : SYZFamily n m) : ∃ σ : ℝ, ∀ (t : Dom m) (x : Dom n) (b : Fin m) (i : Fin n),
    volDens (S.F t) x * ∑ j, (gInd (S.F t) x)⁻¹ i j * thetaM S.F b t x j =
      σ * Kf S (update (vX m) i (vT n b)) (t, x) := by
  have key : ∀ t x b i, reVol S (t, x) * (volDens (S.F t) x *
      ∑ j, (gInd (S.F t) x)⁻¹ i j * thetaM S.F b t x j) =
      -|reVol S (t, x)| * Kf S (update (vX m) i (vT n b)) (t, x) := by
    intro t x b i
    have hs := S.slag t x
    have h := mclean (fun k => D (S.F t) k x) (D (fun s => S.F s x) b t) hs.1 hs.2
      (S.immersed t x) i
    have hre : (hVol fun k => D (S.F t) k x).re = reVol S (t, x) := by
      unfold reVol; rw [frame_eq]
    have hK : kappa (update (fun k => D (S.F t) k x) i (D (fun s => S.F s x) b t)) =
        Kf S (update (vX m) i (vT n b)) (t, x) := by
      unfold Kf
      rw [cols_update (fderiv ℝ (Phi S) (t, x)), frame_eq, DFt_eq]
    rw [hre, hK] at h
    exact h
  rcases sign_const (reVol S) (reVol_cont S) (reVol_ne S) with hpos | hneg
  · refine ⟨-1, fun t x b i => ?_⟩
    have := key t x b i
    rw [abs_of_pos (hpos _)] at this
    have hp := hpos (t, x)
    nlinarith [this]
  · refine ⟨1, fun t x b i => ?_⟩
    have := key t x b i
    rw [abs_of_neg (hneg _)] at this
    have hp := hneg (t, x)
    nlinarith [this]

end Glue

section Glue2

variable {n m : ℕ}

lemma formPair_vol {k : ℕ} (f : Dom k → Amb k) (α β : Dom k → Fin k → ℝ) (x : Dom k) :
    formPair f α β x * volDens f x =
      ∑ i, α x i * (volDens f x * ∑ j, (gInd f x)⁻¹ i j * β x j) := by
  unfold formPair
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma gInd_inv_symm {k : ℕ} (f : Dom k → Amb k) (x : Dom k) (i j : Fin k) :
    (gInd f x)⁻¹ i j = (gInd f x)⁻¹ j i := by
  have hT : (gInd f x).transpose = gInd f x := by
    ext a b; simp [gInd, gAmb_comm]
  have := Matrix.transpose_nonsing_inv (gInd f x)
  rw [hT] at this
  calc (gInd f x)⁻¹ i j = (gInd f x)⁻¹.transpose i j := by rw [this]
    _ = (gInd f x)⁻¹ j i := rfl

lemma gMod_symm {k m : ℕ} (F : Dom m → Dom k → Amb k) (a b : Fin m) (t : Dom m) :
    gMod F a b t = gMod F b a t := by
  unfold gMod L2pair
  congr 1; funext x; congr 1
  unfold formPair
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [gInd_inv_symm]; ring

/-- the periods of `θ^a` and the fluxes of `κ(e, i ← ∂_b F)` -/
noncomputable def Pf (S : SYZFamily n m) (a : Fin m) (i : Fin n) : Dom m → ℝ :=
  fun t => period (thetaM S.F a t) i

noncomputable def Yf (S : SYZFamily n m) (b : Fin m) (i : Fin n) : Dom m → ℝ :=
  fun t => ∫ x in cube n, Kf S (update (vX m) i (vT n b)) (t, x)

lemma Pf_diff (S : SYZFamily n m) (a : Fin m) (i : Fin n) : Differentiable ℝ (Pf S a i) :=
  fun t => (hasFDerivAt_integral_cube (fun t x => thetaM S.F a t x i) (theta_smooth S a i) t).differentiableAt

lemma Yf_diff (S : SYZFamily n m) (b : Fin m) (i : Fin n) : Differentiable ℝ (Yf S b i) :=
  fun t => (hasFDerivAt_integral_cube (fun t x => Kf S (update (vX m) i (vT n b)) (t, x))
    (Kf_smooth S _) t).differentiableAt

lemma theta_smooth_x (S : SYZFamily n m) (a : Fin m) (t : Dom m) (i : Fin n) :
    ContDiff ℝ 1 (fun x => thetaM S.F a t x i) := by
  simp only [thetaM_eq]
  exact kForm_smooth _ _ ((cols_smooth S _).comp ((contDiff_const (c := t)).prodMk contDiff_id))
    ((cols_smooth S _).comp ((contDiff_const (c := t)).prodMk contDiff_id))

lemma Kf_smooth_x (S : SYZFamily n m) (u : Fin n → Dom m × Dom n) (t : Dom m) :
    ContDiff ℝ 1 (fun x => Kf S u (t, x)) :=
  (Kf_smooth S u).comp ((contDiff_const (c := t)).prodMk contDiff_id)

/-- **The moduli metric in cohomological form**: `g_ab = σ Σᵢ [θ^a]ᵢ ∫ Kᵇᵢ`. -/
theorem gMod_eq (S : SYZFamily n m) (σ : ℝ)
    (hσ : ∀ (t : Dom m) (x : Dom n) (b : Fin m) (i : Fin n),
      volDens (S.F t) x * ∑ j, (gInd (S.F t) x)⁻¹ i j * thetaM S.F b t x j =
        σ * Kf S (update (vX m) i (vT n b)) (t, x))
    (a b : Fin m) (t : Dom m) :
    gMod S.F a b t = σ * ∑ i, Pf S a i t * Yf S b i t := by
  have hθs : ∀ i, ContDiff ℝ 1 (fun x => thetaM S.F a t x i) := fun i => theta_smooth_x S a t i
  have hJs : ∀ i, ContDiff ℝ 1 (fun x => σ * Kf S (update (vX m) i (vT n b)) (t, x)) :=
    fun i => contDiff_const.mul (Kf_smooth_x S _ t)
  have hθp : ∀ a' x i, thetaM S.F a t (x + basis a') i = thetaM S.F a t x i := by
    intro a' x i; simp only [thetaM_eq, fderiv_Phi_periodic]
  have hJp : ∀ a' x i, σ * Kf S (update (vX m) i (vT n b)) (t, x + basis a') =
      σ * Kf S (update (vX m) i (vT n b)) (t, x) := by
    intro a' x i; simp only [Kf_periodic]
  have hdiv : ∀ x, ∑ i, D (fun y => σ * Kf S (update (vX m) i (vT n b)) (t, y)) i x = 0 := by
    intro x
    have := (S.harmonic t b).2 x
    simp only [hσ] at this
    exact this
  have hP := pairing (thetaM S.F a t) (fun x i => σ * Kf S (update (vX m) i (vT n b)) (t, x))
    hθs hJs hθp hJp (S.harmonic t a).1 hdiv
  unfold gMod L2pair
  simp only [formPair_vol, hσ]
  rw [hP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  simp only [Pf, Yf, period]
  ring

/-- the fluxes have symmetric derivatives: `∂_c Yᵇᵢ = ∂_b Yᶜᵢ` (from `d(F^*κ) = 0`) -/
theorem DY_symm (S : SYZFamily n m) (b c : Fin m) (i : Fin n) (t : Dom m) :
    D (Yf S b i) c t = D (Yf S c i) b t := by
  set ub := update (vX m) i (vT n b)
  set uc := update (vX m) i (vT n c)
  have h1 : D (Yf S b i) c t = ∫ x in cube n, fderiv ℝ (Kf S ub) (t, x) (vT n c) := by
    rw [show Yf S b i = fun s => ∫ x in cube n, (fun s x => Kf S ub (s, x)) s x from rfl,
      D_integral_cube (fun s x => Kf S ub (s, x)) (Kf_smooth S ub)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact D_left (Kf S ub) t x ((Kf_smooth S ub).differentiable (by norm_num) _) c
  have h2 : D (Yf S c i) b t = ∫ x in cube n, fderiv ℝ (Kf S uc) (t, x) (vT n b) := by
    rw [show Yf S c i = fun s => ∫ x in cube n, (fun s x => Kf S uc (s, x)) s x from rfl,
      D_integral_cube (fun s x => Kf S uc (s, x)) (Kf_smooth S uc)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact D_left (Kf S uc) t x ((Kf_smooth S uc).differentiable (by norm_num) _) b
  have hc : ∀ (u : Fin n → Dom m × Dom n) (w : Dom m × Dom n),
      Continuous (fun x : Dom n => fderiv ℝ (Kf S u) (t, x) w) := fun u w =>
    (((Kf_smooth S u).continuous_fderiv (by norm_num)).clm_apply continuous_const).comp
      (continuous_const.prodMk continuous_id)
  rw [h1, h2, ← sub_eq_zero, ← integral_sub (intOn_cube (hc _ _)) (intOn_cube (hc _ _))]
  have hpt : ∀ x : Dom n, fderiv ℝ (Kf S ub) (t, x) (vT n c) - fderiv ℝ (Kf S uc) (t, x) (vT n b) =
      ∑ j ∈ Finset.univ.erase i,
        D (fun y => Kf S (update (update (vX m) i (vT n b)) j (vT n c)) (t, y)) j x := by
    intro x
    have h := dFkappa (Phi S) (Phi_smooth S) (vX m) (vT n b) (vT n c) i (t, x)
    refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
    exact (D_right (Kf S _) t x ((Kf_smooth S _).differentiable (by norm_num) _) j).symm
  simp only [hpt]
  rw [integral_finsetSum _ (fun j _ => intOn_cube (by
    have := hc (update (update (vX m) i (vT n b)) j (vT n c)) (vX m j)
    refine this.congr fun x => ?_
    exact (D_right (Kf S _) t x ((Kf_smooth S _).differentiable (by norm_num) _) j).symm))]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact integral_cube_D_eq_zero _ (Kf_smooth_x S _ t)
    (fun a x => Kf_periodic S _ t x a) j

lemma D_sigma_sum_mul {k : ℕ} (σ : ℝ) (u v : Fin n → Dom k → ℝ) (t : Dom k) (c : Fin k)
    (hu : ∀ i, DifferentiableAt ℝ (u i) t) (hv : ∀ i, DifferentiableAt ℝ (v i) t) :
    D (fun s => σ * ∑ i, u i s * v i s) c t =
      σ * ∑ i, (u i t * D (v i) c t + v i t * D (u i) c t) := by
  have H := (HasFDerivAt.fun_sum (u := Finset.univ) (A := fun i s => u i s * v i s)
    (fun i _ => (hu i).hasFDerivAt.mul (hv i).hasFDerivAt)).const_mul σ
  unfold D
  rw [H.fderiv]
  simp [smul_eq_mul]

/-- **eq34**: `∂_a g_bc = ∂_b g_ac`. -/
theorem eq34_lib (S : SYZFamily n m) (a b c : Fin m) (t : Dom m) :
    D (fun s => gMod S.F b c s) a t = D (fun s => gMod S.F a c s) b t := by
  obtain ⟨σ, hσ⟩ := mclean_family S
  have hg : ∀ a b, (fun s => gMod S.F a b s) = fun s => σ * ∑ i, Pf S a i s * Yf S b i s :=
    fun a b => funext fun s => gMod_eq S σ hσ a b s
  have hT : ∀ a b c, D (fun s => gMod S.F a b s) c t = σ * ∑ i, Pf S a i t * D (Yf S b i) c t := by
    intro a b c
    rw [hg, D_sigma_sum_mul σ (fun i => Pf S a i) (fun i => Yf S b i) t c
      (fun i => Pf_diff S a i t) (fun i => Yf_diff S b i t)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have h0 : D (Pf S a i) c t = 0 := S.periodConst a i c t
    rw [h0, mul_zero, add_zero]
  have hbc : ∀ a b c, D (fun s => gMod S.F a b s) c t = D (fun s => gMod S.F a c s) b t := by
    intro a b c
    rw [hT, hT]
    simp only [DY_symm S b c]
  have hab : ∀ a b c, D (fun s => gMod S.F a b s) c t = D (fun s => gMod S.F b a s) c t := by
    intro a b c
    rw [show (fun s => gMod S.F a b s) = fun s => gMod S.F b a s from
      funext fun s => gMod_symm S.F a b s]
  rw [hbc b c a, hab b a c, hbc a b c]

theorem kahler_lib (S : SYZFamily n m) :
    IsClosed2Form (moduliKahler (fun t => Matrix.of fun a b => gMod S.F a b t)) := by
  obtain ⟨σ, hσ⟩ := mclean_family S
  refine closed_of_symm _ (fun a b => ?_) (fun a b c t => eq34_lib S a b c t)
  have : (fun t => (Matrix.of fun a b => gMod S.F a b t) a b) =
      fun s => σ * ∑ i, Pf S a i s * Yf S b i s :=
    funext fun s => gMod_eq S σ hσ a b s
  rw [this]
  exact (Differentiable.const_mul (Differentiable.fun_sum fun i _ =>
    (Pf_diff S a i).mul (Yf_diff S b i)) σ)

end Glue2

end SYZL

set_option maxHeartbeats 4000000 in
open SYZ in
theorem solution {n m : ℕ}
    (S : SYZFamily n m) (a b c : Fin m) (t : Dom m) :
    D (fun s => gMod S.F b c s) a t = D (fun s => gMod S.F a c s) b t := by
  exact SYZL.eq34_lib S a b c t
